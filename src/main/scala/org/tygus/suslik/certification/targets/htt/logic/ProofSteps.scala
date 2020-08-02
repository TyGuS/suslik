package org.tygus.suslik.certification.targets.htt.logic

import org.tygus.suslik.certification.targets.htt.language.Types._
import org.tygus.suslik.certification.targets.htt.language.Expressions._
import org.tygus.suslik.certification.targets.htt.logic.Proof._
import org.tygus.suslik.certification.targets.htt.logic.Sentences._

object ProofSteps {

  // Generate right-associative destructing pattern for a tuple of Coq expressions
  def nestedDestructR(items: Seq[CExpr]): String = items match {
    case Seq(e1, e2, rest @ _*) =>
      s"[${e1.pp} ${nestedDestructR(e2 +: rest)}]"
    case Seq(e, _*) =>
      e.pp
    case Seq() =>
      ""
  }

  // Generate left-associative destructing pattern for a tuple of Coq expressions
  def nestedDestructL(items: Seq[CExpr]): String = {
    def visit(items: Seq[CExpr]): String = items match {
        case Seq(e1, e2, rest @ _*) =>
          s"[${visit(e2 +: rest)} ${e1.pp}]"
        case Seq(e, _*) =>
          e.pp
        case Seq() =>
          ""
      }
    visit(items.reverse)
  }

  sealed abstract class ProofStep {
    def pp: String = ""

    /**
      * Retroactively refresh any ghost variables that were instantiated after this proof step was first generated
 *
      * @param sbst the certification environment
      * @return the new proof step
      */
    def refreshGhostVars(sbst: SubstVar): ProofStep = this

    /**
      * Move a sequence of existential terms from goal to context
      * @param builder the string builder
      * @param ex the existential terms
      * @param nested whether or not to format the existentials as tuples
      */
    protected def elimExistentials(builder: StringBuilder, ex: Seq[CExpr], nested: Boolean = false): Unit = {
      if (ex.nonEmpty) {
        if (nested) {
          builder.append(s"move=>${nestedDestructL(ex)}.\n")
        } else {
          builder.append(s"move=>${ex.map(v => s"[${v.pp}]").mkString(" ")}.\n")
        }
      }
    }

    /**
      * Given a precondition assertion, move all terms to the context
      * @param builder the string builder
      * @param asn the precondition assertion
      * @param uniqueName a unique identifier
      */
    protected def initPre(builder: StringBuilder, asn: CAssertion, uniqueName: String): Unit = {
      val phi = asn.phi
      val sigma = asn.sigma
      val phiName = s"phi_$uniqueName"
      val sigmaName = s"sigma_$uniqueName"

      // move pure part to context
      if (!phi.isTrivial) {
        builder.append(s"move=>[$phiName].\n")
      }

      // move spatial part to context, and then substitute where appropriate
      builder.append(s"move=>[$sigmaName].\n")
      builder.append(s"rewrite->$sigmaName in *.\n")

      // move predicate apps to context, if any
      if (sigma.apps.nonEmpty) {
        val appNames = sigma.apps.map(app => CVar(app.hypName))
        val hApps = nestedDestructR(appNames)
        builder.append(s"move=>$hApps.\n")
      }
    }

    /**
      * Execute the correct sequence of existential eliminations and constructor unfoldings needed to
      * transform the goal into a given post condition assertion
      * @param builder the string builder
      * @param asn an assertion (or part of an assertion) in the post condition
      * @param ex a sequence of existentials to eliminate
      * @param unfoldings a map from predicate applications to their unfolded state
      */
    protected def solvePost(builder: StringBuilder, asn: CAssertion, ex: Seq[CExpr], unfoldings: Unfoldings): Unit = {
      // Eliminate value existentials
      if (ex.nonEmpty) {
        builder.append(s"exists ${ex.map(v => s"(${v.pp})").mkString(", ")};\n")
      }

      /**
        * Existentials for the current assertion need to be provided eagerly, so look ahead to find out
        * the maximally unfolded, "flattened" form of the heap
        * @param app the predicate app to flatten
        * @return the points-to's and pred apps in the unfolded heap; any pred apps that remain have already been
        *         established as facts earlier on, so there is no need to unfold further
        */
      def toUnfoldedHeap(app: CSApp): (Seq[CPointsTo], Seq[CSApp]) = unfoldings.get(app) match {
        case Some(a) =>
          val sigma = a.asn.sigma
          val (ptss, apps) = sigma.apps.map(toUnfoldedHeap).unzip
          (sigma.ptss ++ ptss.flatten, apps.flatten)
        case None =>
          (Seq.empty, Seq(app))
      }

      // Eliminate heap existentials (one for each predicate application in the assertion)
      val apps = asn.sigma.apps
      for (app <- apps) {
        val (unfoldedPtss, unfoldedApps) = toUnfoldedHeap(app)
        val h = CSFormula("", unfoldedApps, unfoldedPtss)
        builder.append(s"exists (${h.ppHeap});\n")
      }

      // Solve everything except the predicate applications
      builder.append("ssl_emp_post.\n")

      // For each predicate application, unfold the correct constructor and recursively solve its expanded form
      for {
        app <- apps
        // If `app` isn't found in the unfoldings, its truth was already established earlier on
        c <- unfoldings.get(app)
      } {
        builder.append(s"unfold_constructor ${c.idx};\n")
        solvePost(builder, c.asn, c.existentials, unfoldings)
      }
    }

    def vars: Set[CVar] = {
      def collector(acc: Set[CVar])(st: ProofStep): Set[CVar] = st match {
        case WriteStep(to, _, e, _) =>
          acc ++ to.vars ++ e.vars
        case ReadStep(to, from) =>
          acc ++ to.vars ++ from.vars
        case AllocStep(to, _, _) =>
          acc ++ to.vars
        case SeqCompStep(s1,s2) =>
          val acc1 = collector(acc)(s1)
          collector(acc1)(s2)
        case CallStep(goal, _) =>
          acc ++ goal.programVars ++ goal.universalGhosts ++ goal.existentials
        case _ =>
          acc
      }

      collector(Set.empty)(this)
    }
  }

  /**
    * Sequentially compose two proof steps
    * @param s1 the first step
    * @param s2 the second step
    */
  case class SeqCompStep(s1: ProofStep, s2: ProofStep) extends ProofStep {
    override def pp: String = s"${s1.pp}${s2.pp}"

    /**
      * The synthesis removes some extraneous program statements that are unused in the final result, but
      * the CertTree retains them as nodes. So, we remove them from our proof script here.
      * @return A simplified proof step
      */
    def simplify: ProofStep = {
      (s1, s2) match {
        case (ReadStep(to, _), _) => simplifyBinding(to)
//        case (WriteStep(to), _) => simplifyBinding(to)
//        case (AllocStep(to, _, _), _) => simplifyBinding(to)
        case _ => this
      }
    }

    def simplifyBinding(newvar: CVar): ProofStep = {
      val used = s2.vars
      if (used.contains(newvar)) {
        this
      } else s2 // Do not generate bindings for unused variables
    }
  }

  /**
    * Perform a write
    * @param to the variable to write to
    * @param offset the variable offset
    * @param e the expression to write
    * @param frame whether or not to frame out the heaplet after writing
    */
  case class WriteStep(to: CVar, offset: Int, e: CExpr, frame: Boolean = true) extends ProofStep {
    override def refreshGhostVars(sbst: SubstVar): WriteStep =
      WriteStep(to.substVar(sbst), offset, e.subst(sbst), frame)

    override def pp: String = {
      val ptr = if (offset == 0) to.pp else s"(${to.pp} .+ $offset)"
      val writeStep = "ssl_write.\n"

      // SSL's `Write` rule does an implicit frame under normal circumstances, but not during a call synthesis
      val writePostStep = if (frame) s"ssl_write_post $ptr.\n" else ""

      writeStep + writePostStep
    }
  }

  /**
    * Perform a read
    * @param to the dst variable
    * @param from the src variable
    */
  case class ReadStep(to: CVar, from: CVar) extends ProofStep {
    override def refreshGhostVars(sbst: SubstVar): ReadStep =
      ReadStep(to.substVar(sbst), from.substVar(sbst))

    override def pp: String = "ssl_read.\n"
  }

  /**
    * Allocate a memory block of size `sz` and bind it to a variable
    * @param to the dst variable
    * @param tpe the alloc type
    * @param sz the size allocated
    */
  case class AllocStep(to: CVar, tpe: HTTType, sz: Int) extends ProofStep {
    override def refreshGhostVars(sbst: SubstVar): AllocStep =
      AllocStep(to.substVar(sbst), tpe, sz)

    override def pp: String = s"ssl_alloc ${to.pp}.\n"
  }

  /**
    * Free a memory block of size `sz`
    * @param size the size of the block to free
    */
  case class FreeStep(size: Int) extends ProofStep {
    override def pp: String = {
      // In HTT, each location offset needs to be freed individually
      val deallocStmts = (1 to size).map(_ => "ssl_dealloc.")
      s"${deallocStmts.mkString("\n")}\n"
    }
  }

  /**
    * Execute the Open rule
    */
  case object OpenStep extends ProofStep {
    override def pp: String = "ssl_open.\n"
  }

  /**
    * Perform clean-up tasks at the start of each branch generated by the Open rule
    * @param app the predicate application used in the Open rule
    * @param pre the precondition for the predicate's constructor that was used for this branch of the Open rule
    * @param preEx the value existentials for this precondition
    */
  case class OpenPostStep(app: CSApp, pre: CAssertion, preEx: Seq[CExpr]) extends ProofStep {
    override def refreshGhostVars(sbst: SubstVar): OpenPostStep = OpenPostStep(
      app.subst(sbst),
      pre.subst(sbst),
      preEx.map(v => v.subst(sbst))
    )

    override def pp: String = {
      val builder = new StringBuilder()
      builder.append(s"ssl_open_post ${app.hypName}.\n")

      elimExistentials(builder, preEx)
      elimExistentials(builder, pre.heapVars)
      initPre(builder, pre, app.uniqueName)

      builder.toString()
    }
  }

  /**
    * Call a function
    * @param goal the goal of the call synthesis
    * @param callId a unique call identifier
    */
  case class CallStep(goal: CGoal, callId: String) extends ProofStep {
    override def refreshGhostVars(sbst: SubstVar): CallStep =
      CallStep(goal.subst(sbst), callId)

    override def pp: String = {
      val builder = new StringBuilder()

      // Move the part of the heap relevant to the call abduction to the beginning
      builder.append(s"ssl_call_pre (${goal.pre.sigma.ppHeap}).\n")

      // Provide the necessary existentials so that the precondition of the call goal is met,
      // and then execute the call
      builder.append(s"ssl_call (${goal.universalGhosts.map(_.pp).mkString(", ")}).\n")
      solvePost(builder, goal.pre, Seq.empty, Map.empty)

      builder.append(s"move=>h_$callId.\n")

      // The postcondition of the call abduction becomes the precondition of the companion
      elimExistentials(builder, goal.existentials)
      elimExistentials(builder, goal.post.heapVars)
      initPre(builder, goal.post, callId)

      // Store validity hypotheses in context
      builder.append("store_valid.\n")

      builder.toString()
    }
  }

  /**
    * Eliminate the program's ghost variables and move them to the proof context
    * @param goal the goal
    */
  case class GhostElimStep(goal: CGoal) extends ProofStep {
    override def refreshGhostVars(sbst: SubstVar): GhostElimStep =
      GhostElimStep(goal.subst(sbst))

    override def pp: String = {
      val builder = new StringBuilder()

      // Pull out any precondition ghosts and move precondition heap to the context
      builder.append("ssl_ghostelim_pre.\n")

      elimExistentials(builder, goal.universalGhosts, nested = true)
      elimExistentials(builder, goal.pre.heapVars)
      initPre(builder, goal.pre, "self")

      // store heap validity assertions
      builder.append("ssl_ghostelim_post.\n")

      builder.toString()
    }
  }

  case object AbduceBranchStep extends ProofStep {
    override def pp: String = "ssl_abduce_branch.\n"
  }

  /**
    * At the end of a branch, transform the goal into the funspec's post-condition
    * @param post the post-condition
    * @param postEx the post-condition's value existentials
    * @param unfoldings a map from predicate applications to their unfolded state
    */
  case class EmpStep(post: CAssertion, postEx: Seq[CExpr], unfoldings: Unfoldings) extends ProofStep {
    override def pp: String = {
      val builder = new StringBuilder()
      builder.append("ssl_emp;\n")
      solvePost(builder, post, postEx, unfoldings)
      builder.toString()
    }
  }
}
