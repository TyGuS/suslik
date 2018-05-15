package org.tygus.synsl.logic

import org.tygus.synsl.language.Expressions.{Expr, Var}

object Unification extends SepLogicUtils with PureLogicUtils {
  
  type Subst = Map[Var, Expr]
  type SubstVar = Map[Var, Var]

  /**
    * Generate fresh names for variables in `source` that occur in `target`
    */
  private def refreshSource(target: UnificationGoal, source: UnificationGoal): (UnificationGoal, SubstVar) = {
    val (freshSourceFormula, freshSubst) = source.formula.refresh(target.formula.vars)
    val freshParams = source.params.map(_.subst(freshSubst)).asInstanceOf[Set[Var]]
    (UnificationGoal(freshSourceFormula, freshParams), freshSubst)
  }

  private def genSubst(to: Expr, from: Expr, taken: Set[Var]): Option[Subst] = {
    if (to == from) Some(Map.empty) else from match {
      case _from@Var(_) =>
        if (!taken.contains(_from)) Some(Map(_from -> to))
        else None
      case _ => None
    }
  }

  private def assertNoOverlap(sbst1: Subst, sbst2: Subst) {
    assert(sbst1.keySet.intersect(sbst2.keySet).isEmpty, s"Two substitutions overlap:\n:$sbst1\n$sbst2")
  }

  /**
    * Tries to unify two heaplets `target` and `source`, assuming `source` has
    * variables that are either free or in `nonFreeInSource`.
    *
    * If successful, returns a substitution from `source`'s fresh variables to `target`'s variables
    */
  def tryUnify(target: Heaplet, source: Heaplet, nonFreeInSource: Set[Var]): Option[Subst] = {
    assert(target.vars.forall(nonFreeInSource.contains), s"Not all variables of ${target.pp} are in $nonFreeInSource")
    (target, source) match {
      case (PointsTo(x@Var(_), o1, y), PointsTo(a@Var(_), o2, b)) =>
        if (o1 != o2) None else {
          assert(nonFreeInSource.contains(x))
          assert(y.vars.forall(nonFreeInSource.contains))
          for {
            m1 <- genSubst(x, a, nonFreeInSource)
            _v2 = b.subst(m1)
            m2 <- genSubst(y, _v2, nonFreeInSource)
          } yield {
            assertNoOverlap(m1, m2)
            m1 ++ m2
          }
        }
      case (Block(x1@Var(_), s1), Block(x2@Var(_), s2)) =>
        if (s1 != s2) None else {
          assert(nonFreeInSource.contains(x1))
          genSubst(x1, x2, nonFreeInSource)
        }
      case (SApp(p1, es1, _), SApp(p2, es2, _))
        // Only unify predicates with variables as arguments
        if es1.forall(_.isInstanceOf[Var]) && es2.forall(_.isInstanceOf[Var]) =>
        if (p1 != p2 || es1.size != es2.size) None else {
          val pairs = es1.zip(es2).asInstanceOf[List[(Var, Var)]]
          // Collect the mapping from the predicate parameters
          pairs.foldLeft(Some(Map.empty): Option[Subst]) {
            case (opt, (x1, x2)) => opt match {
              case None => None
              case Some(acc) => genSubst(x1, x2, nonFreeInSource) match {
                case Some(sbst) =>
                  assertNoOverlap(acc, sbst)
                  Some(acc ++ sbst)
                case None => None
              }
            }
          }
        }
      case _ => None
    }
  }


  /**
    * Check that two lists of heaplets have a chance to be unified
    */
  private def checkShapesMatch(cs1: List[Heaplet], cs2: List[Heaplet]): Boolean = {
    val (ps1, ps2) = (cs1.filter(_.isInstanceOf[PointsTo]), cs2.filter(_.isInstanceOf[PointsTo]))
    val (bs1, bs2) = (cs1.filter(_.isInstanceOf[Block]), cs2.filter(_.isInstanceOf[Block]))
    val (as1, as2) = (cs1.filter(_.isInstanceOf[SApp]), cs2.filter(_.isInstanceOf[SApp]))

    // Check sizes
    if (ps1.size != ps2.size) return false
    if (bs1.size != bs2.size) return false
    if (as1.size != as2.size) return false

    // Check matching blocks
    val checkMatchingBlocks = (bs1: List[Heaplet], bs2: List[Heaplet]) =>
      bs1.forall {
        case Block(_, s1) => bs2.exists { case Block(_, s2) => s1 == s2; case _ => false }
        case _ => false
      }

    if (!checkMatchingBlocks(bs1, bs2) || !checkMatchingBlocks(bs2, bs1)) return false

    // Check matching blocks
    val checkMatchingApps = (as1: List[Heaplet], as2: List[Heaplet]) =>
      as1.forall {
        case SApp(x1, xs1, _) =>
          as2.exists { case SApp(x2, xs2, _) => x1 == x2 && xs1.size == xs2.size; case _ => false }
        case _ => false
      }
    if (!checkMatchingApps(as1, as2) || !checkMatchingApps(as2, as1)) return false

    true
  }

  /**
    * The result is a mapping of variables in the `source` to the variables in the `target`,
    * with the constraint that parameters of the former are not instantiated with the ghosts
    * of the latter (instantiating ghosts with anything is fine).
    */
  def unify(target: UnificationGoal, source: UnificationGoal): Option[(Assertion, Subst)] = {
    // Make sure that all variables in target are fresh wrt. source
    val (freshSource, freshSubst) = refreshSource(target, source)

    val tFormula = target.formula
    val targetChunks = tFormula.sigma.chunks
    val sFormula = freshSource.formula
    val sourceChunks = sFormula.sigma.chunks
    val takenVars = tFormula.vars

    if (!checkShapesMatch(targetChunks, sourceChunks)) return None

    /**
      * Check that substitution does not substitutes ghosts for params
      */
    def checkSubstWF(sbst: Subst) = {
      val tParams = target.params
      val tGhosts = target.ghosts
      assert(tParams.intersect(tGhosts).isEmpty, s"Non empty sets: $tParams, $tGhosts")
      val sParams = freshSource.params
      val sGhosts = freshSource.ghosts
      assert(sParams.intersect(sGhosts).isEmpty, s"Non empty sets: $sParams, $sGhosts")
      sbst.forall { case (from, to) =>
        // If "to" is a ghost (in the target), the "from" also should be a ghost (in the source)
        (tGhosts.intersect(to.vars).isEmpty || sGhosts.contains(from)) &&
          // If "from" is a parameter (in the source), the "to" also should be a parameter (in the target)
          (!sParams.contains(from) || to.vars.forall(tParams.contains))
      }
    }

    /**
      * Tries to find amoungst chunks a heaplet h', which can be unified with the heaplet h.
      * If successful, returns a substitution and a list of remaining heaplets
      */
    def findChunkAndUnify(h: Heaplet, chunks: List[Heaplet]): Option[(Subst, List[Heaplet])] = {
      val iter = chunks.iterator
      while (iter.hasNext) {
        val candidate = iter.next()
        tryUnify(h, candidate, takenVars) match {
          case Some(sbst) if checkSubstWF(sbst) => // found a good substitution
            // Return it and remaining chunks with the applied substitution
            val remainingHeapletsAdapted = chunks.filter(_ != candidate).map(_.subst(sbst))
            return Some(sbst, remainingHeapletsAdapted)
          case _ => // Do nothing
        }
      }
      None
    }

    // Invariant: none of the keys in acc are present in sourceChunks
    def unifyGo(targetChunks: List[Heaplet], sourceChunks: List[Heaplet], acc: Subst): Option[Subst] = targetChunks match {
      case Nil =>
        // No more source chunks to unify
        if (sourceChunks.isEmpty) Some(acc) else None
      case tc :: tcss => findChunkAndUnify(tc, sourceChunks) match {
        case None => None
        // Could not find a matching heaplet
        case Some((sbst, scsUpdated)) =>
          assertNoOverlap(acc, sbst)
          unifyGo(tcss, scsUpdated, acc ++ sbst)
      }
    }

    // Lazily try all permutations of source chunks
    // Ugly imperative stuff below
    val iter = targetChunks.permutations
    while (iter.hasNext) {
      val tChunks = iter.next()
      unifyGo(tChunks, sourceChunks, Map.empty) match {
        case Some(newSubst) =>
          // Found unification, see if it captures all variables in the pure part
          val newAssertion = sFormula.subst(newSubst)
          if (newAssertion.vars.forall(tFormula.vars.contains(_))) {
            // No free variables after substitution => successful unification
            /*
            TODO: Check via external prover that the new target pure part is implied by the source pure part, i.e.,
             sFormula.phi implies newAssertion.phi
             */
            return Some((newAssertion, compose(freshSubst, newSubst)))
          }
        // Otherwise, continue
        case None =>
      }
    }
    None
  }

  def compose(subst1: SubstVar, subst2: Subst): Subst = {
    subst1.map { case (k, v) => k -> subst2.getOrElse(v, v) }
  }

  def ppSubst(m: Subst): String = {
    s"{${m.map{case (k, v) => s"${k.pp} -> ${v.pp}"}.mkString("; ")}}"
  }
}

/**
  * A parameterized formula, for which unification produces the substitution
  */
case class UnificationGoal(formula: Assertion, params: Set[Var]) {
  def ghosts: Set[Var] = formula.vars -- params

  override def toString: String = s"(${params.map(_.pp).mkString(", ")}) ${formula.pp}"
}
