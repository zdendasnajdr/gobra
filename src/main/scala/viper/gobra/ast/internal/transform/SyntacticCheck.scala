// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.gobra.ast.internal.transform

import viper.gobra.ast.{internal => in}

/**
  * Transformation responsible for generating call-graph edges from interface methods to their implementations' methods.
  * This is necessary to soundly verify termination in the presence of dynamic method binding.
  */
object SyntacticCheck extends InternalTransform {
  override def name(): String = "syntactic_check_for_slices"

  /**
    * Program-to-program transformation
    */
  override def transform(p: in.Program): in.Program = p match {
    case in.Program(_, members, _) =>

      def checkBody(m: in.Member): Unit = m match {
        case m: in.Function =>
          m.body match {
            case Some(in.MethodBody(_, seqn, _)) =>
              seqn.stmts.foreach(
                s => s.visit {
                  case elem: in.Stmt =>
                    if (checkStmt(elem)) {
                      println("The function " + m.name + " contains subslicing expressions")
                      return
                    } else {}
                  case _ =>
              })
              println("The function " + m.name + " does not contain subslicing expressions")
            case _ => println("The function " + m.name + " does not contain subslicing expressions")
          }
        case _ =>
      }

      /*
      Checks the expressions for subslicing expressions
       */
      def checkExpr(e: in.Expr): Boolean = {
        var slice = false
        e.visit {
          case elem: in.Slice => slice = true
          case _ =>
        }
        slice
      }

      /*
      Checks the statements for subslicing expressions
       */
      def checkStmt(s: in.Stmt): Boolean = s match {
        case s: in.If => checkExpr(s.cond) || checkStmt(s.thn) || checkStmt(s.els)
        case s: in.While =>  checkExpr(s.cond) || checkStmt(s.body)
        case s: in.SingleAss => checkExpr(s.right)
        case s: in.FunctionCall => s.args.exists(e => checkExpr(e))
        case s: in.MethodCall => s.args.exists(e => checkExpr(e))
        case _ => false
      }

      members.foreach(checkBody)

    in.Program(
      types = p.types,
      members = p.members,
      table = p.table,
    )(p.info)
  }
}
