package org.tygus.suslik.certification.targets.vst

import java.io.{BufferedOutputStream, BufferedReader, ByteArrayInputStream, ByteArrayOutputStream, File, FileOutputStream, FileWriter, InputStreamReader, StringWriter}

import org.tygus.suslik.certification.CertTree
import org.tygus.suslik.synthesis.{AppendProducer, BranchProducer, ChainedProducer, ConstProducer, ExtractHelper, GhostSubstProducer, GuardedProducer, HandleGuard, IdProducer, PartiallyAppliedProducer, PrependFromSketchProducer, PrependProducer, SeqCompProducer, StmtProducer, SubstProducer, UnfoldProducer}
import scalaz.Scalaz.{ToTraverseOps, ToTraverseOpsUnapply}

import scala.io._
import scala.sys.process._
import scala.sys.process.ProcessLogger

object Debug {


  def dotbin(format: String)(dot: String): Array[Byte] = {
    val process = "dot -Gdpi=300 -T" + format
    val bos = new ByteArrayOutputStream()
    val exitCode = process #< new ByteArrayInputStream(dot.getBytes) #> bos !< ProcessLogger(s => ())
    if (exitCode == 0) {
      bos.toByteArray()
    }
    else {
      throw new RuntimeException("Nonzero exit value (" + exitCode + ") for '" + process + "' with: " + dot)
    }
  }

  def stmt_producer_node_to_text(stmtProducer: StmtProducer): String = stmtProducer match {
    case ChainedProducer(p1, p2) => s"ChainedProducer [${stmtProducer.arity}]"
    case PartiallyAppliedProducer(p, s) => s"PartiallyAppliedProducer [${stmtProducer.arity}] (${s.toString()})"
    case IdProducer => s"IdProducer[${stmtProducer.arity}]"
    case ConstProducer(s) => s"ConstProducer[${stmtProducer.arity}](${s.pp})"
    case PrependProducer(s) => s"PrependProducer[${stmtProducer.arity}](${s.pp})"
    case PrependFromSketchProducer(s) => s"PrependFromSketchProducer[${stmtProducer.arity}](${s.pp})"
    case AppendProducer(s) => s"AppendProducer[${stmtProducer.arity}](${s.pp})"
    case SeqCompProducer => "SeqCompProducer[${stmtProducer.arity}]"
    case ExtractHelper(goal) => s"ExtractHelper[${stmtProducer.arity}](${"<opaque>"})"
    case HandleGuard(goal) => s"HandleGuard[${stmtProducer.arity}](${"<See goal>"})"
    case BranchProducer(_, _, _, selectors) => s"BranchProducer[${stmtProducer.arity}] {\n${selectors.map(_.pp).mkString("\n")}\n}"
    case GuardedProducer(cond, goal) =>
      s"GuardedProducer[${stmtProducer.arity}] {\n cond=${cond.pp}\n goal=${goal.pp}\n}"
    case SubstProducer(subst) => s"SubstProducer[${stmtProducer.arity}](${subst.toString})"
    case GhostSubstProducer(subst) => s"GhostSubstProducer[${stmtProducer.arity}](${subst.toString})"
    case UnfoldProducer(app, selector, asn, substEx) =>
      s"UnfoldProducer[${stmtProducer.arity}] {\n app=${app.pp}\n selector=${selector.pp}\n asn=${asn.toString}\n substEx=${substEx.toString}\n}"
  }


  def visualize_proof_tree(stmtProducer: StmtProducer): Unit = {
    var nodes: List[(String, String)] = Nil
    var edges: List[(String, String)] = Nil
    var same_ranks: List[List[String]] = Nil
    var count = 0

    def next_id(x: Unit): String = {
      count = count + 1
      s"node_${count}"
    }

    def process_producer(root_node: Option[String])(stmtProducer: StmtProducer): String = {
      val node_id = next_id()
      val node_text = stmt_producer_node_to_text(stmtProducer)
      nodes = (node_id, node_text) :: nodes
      root_node match {
        case Some(value) => edges = (value, node_id) :: edges
        case None => ()
      }
      stmtProducer match {
        case ChainedProducer(p1, p2) =>
          val child1 = process_producer(Some(node_id))(p1)
          val child2 = process_producer(Some(node_id))(p2)
          same_ranks = List(child1, child2) :: same_ranks
        case PartiallyAppliedProducer(p, s) =>
          process_producer(Some(node_id))(p)
        case _ => ()
      }
      node_id
    }

    process_producer(None)(stmtProducer)

    val graph_dot_spec =
      s"""
         |digraph proof_tree {
         |  size="10,10";
     ${nodes.map({ case (node_id, node_text) => s"  |  ${node_id} [label=${"\"" ++ node_text ++ "\""}]" }).mkString("\n")}
         |
     ${edges.map({ case (fro_n, to_n) => s"  |  ${fro_n} -> ${to_n}" }).mkString("\n")}
         |
     ${same_ranks.map((ls => s" | { rank=same; ${ls.mkString(" ")} }")).mkString("\n")}
         |}
         |""".stripMargin

    visualize_dot_viz_spec(graph_dot_spec)

  }


  def visualize_ctree(root: CertTree.Node): Unit = {
    var nodes: List[(String, String)] = Nil
    var edges: List[(String, String)] = Nil
    var same_ranks: List[List[String]] = Nil
    var count = 0

    def next_id(x: Unit): String = {
      count = count + 1
      s"node_${count}"
    }

    def process_producer(root_node: Option[String])(stmtProducer: StmtProducer): State[CertTree.Node, String] = {
      val node_id = next_id()
      val node_text = stmt_producer_node_to_text(stmtProducer)
      nodes = (node_id, node_text) :: nodes
      root_node match {
        case Some(value) => edges = (value, node_id) :: edges
        case None => ()
      }
      for {
        _ <- (stmtProducer match {
          case ChainedProducer(p1, p2) =>
            for {
              child1 <- process_producer(Some(node_id))(p1)
              child2 <- process_producer(Some(node_id))(p2)
              _ <- State.ret(same_ranks = List(child1, child2) :: same_ranks)
            } yield ()
          case PartiallyAppliedProducer(p, s) => for {
            _ <- process_producer(Some(node_id)) (p)
          } yield ()
          case BranchProducer(_, _, _, selectors) =>for {
            _ <- State.mapM(selectors.toList)(_ => for {
              child <- State.pop[CertTree.Node]
              result <- process_root(Some(node_id))(child: CertTree.Node)
            } yield result)
          } yield ()

          case GuardedProducer(cond, _) => for {
            if_true <- State.pop[CertTree.Node]
            if_false <- State.pop[CertTree.Node]
            _ <- process_root(Some(node_id))(if_true)
            _ <- process_root(Some(node_id))(if_false)
          } yield ()
          case HandleGuard(_) => State.ret(())
          case ConstProducer(_) => State.ret(())
          case ExtractHelper(_) => State.ret(())
          case IdProducer => for {
            child <- State.pop[CertTree.Node]
            result <- process_root(Some(node_id))(child)
          } yield ()


          case PrependProducer(_) => for {
            child <- State.pop[CertTree.Node]
            result <- process_root(Some(node_id))(child)
          } yield ()

          case v => for {
            _ <- State.mapM(List.range(1, v.arity))(_ => for {
              child <- State.pop[CertTree.Node]
              result <- process_root(Some(node_id))(child: CertTree.Node)
            } yield result)
          } yield ()
        })  : State[CertTree.Node, Unit]
        result <- State.ret(node_id)
      } yield result
    }
    def process_root(parent:Option[String])(node: CertTree.Node) : State[CertTree.Node, String] = {
      for {
        _ <- State.push_multi(node.children)
        result <- process_producer(parent)(node.kont)
      } yield result
    }

    process_root(None)(root).eval(Nil)

    val graph_dot_spec =
      s"""
         |digraph proof_tree {
         |  size="10,10";
     ${nodes.map({ case (node_id, node_text) => s"  |  ${node_id} [label=${"\"" ++ node_text ++ "\""}]" }).mkString("\n")}
         |
     ${edges.map({ case (fro_n, to_n) => s"  |  ${fro_n} -> ${to_n}" }).mkString("\n")}
         |
     ${same_ranks.map((ls => s" | { rank=same; ${ls.mkString(" ")} }")).mkString("\n")}
         |}
         |""".stripMargin

    visualize_dot_viz_spec(graph_dot_spec)

  }


  private def visualize_dot_viz_spec(graph_dot_spec: String) = {
    val dot_bin: Array[Byte] = dotbin("png")(graph_dot_spec)

    val image_file: File = {
      val file = File.createTempFile("suslik_visualizer", ".png")
      val out = new BufferedOutputStream(new FileOutputStream(file))
      out.write(dot_bin)
      out.close()
      file
    }
    val cmd = "feh " ++ image_file.toPath.toAbsolutePath.toString
    cmd !!
  }
}
