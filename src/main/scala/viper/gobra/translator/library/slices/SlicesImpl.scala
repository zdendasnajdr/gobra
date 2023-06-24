// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2020 ETH Zurich.

package viper.gobra.translator.library.slices

import viper.gobra.translator.library.arrays.Arrays
import viper.silver.{ast => vpr}

class SlicesImpl(val arrays : Arrays) extends Slices {
  private val domainName : String = "Slice"
  private val typeVar : vpr.TypeVar = vpr.TypeVar("T")
  private val domainType: vpr.DomainType = vpr.DomainType(domainName, Map[vpr.TypeVar, vpr.Type](typeVar -> typeVar))(Seq(typeVar))

  private lazy val sadd_func = sadd_func_def()

  /**
    * Determines whether the "Slice" Viper domain
    * should be generated upon finalisation.
    */
  private var generateDomain : Boolean = false

  /**
    * {{{
    * function sarray(s : Slice[T]) : ShArray[T]
    * }}}
    */
  private lazy val sarray_func : vpr.DomainFunc = vpr.DomainFunc(
    "sarray",
    Seq(vpr.LocalVarDecl("s", domainType)()),
    arrays.typ(typeVar)
  )(domainName = domainName)

  /**
    * {{{
    * function soffset(s : Slice[T]) : Int
    * }}}
    */
  private lazy val soffset_func : vpr.DomainFunc = vpr.DomainFunc(
    "soffset",
    Seq(vpr.LocalVarDecl("s", domainType)()),
    vpr.Int
  )(domainName = domainName)

  /**
    * {{{
    * function slen(s : Slice[T]) : Int
    * }}}
    */
  private lazy val slen_func : vpr.DomainFunc = vpr.DomainFunc(
    "slen",
    Seq(vpr.LocalVarDecl("s", domainType)()),
    vpr.Int
  )(domainName = domainName)

  /**
    * {{{
    * function scap(s : Slice[T]) : Int
    * }}}
    */
  private lazy val scap_func : vpr.DomainFunc = vpr.DomainFunc(
    "scap",
    Seq(vpr.LocalVarDecl("s", domainType)()),
    vpr.Int
  )(domainName = domainName)

  /**
   * {{{
   *   function sloc(s: Slice[T], i: Int) : T
   * }}}
   */
  private lazy val sloc_func: vpr.DomainFunc = vpr.DomainFunc(
    "sloc",
    Seq(vpr.LocalVarDecl("s", domainType)(), vpr.LocalVarDecl("i", vpr.Int)()),
    typeVar
  )(domainName = domainName)

  /**
    * {{{
    * function smake(len: Int, cap: Int): Slice[T]
    * }}}
    */
  private lazy val smake_func : vpr.DomainFunc = vpr.DomainFunc(
    "smake",
    Seq(vpr.LocalVarDecl("l", vpr.Int)(), vpr.LocalVarDecl("c", vpr.Int)()),
    domainType
  )(domainName = domainName)

  /**
   * {{{
   *   function sfirst(r: T): Slice[T]
   * }}}
   */
  private lazy val sfirst_func: vpr.DomainFunc = vpr.DomainFunc(
    "sfirst",
    Seq(vpr.LocalVarDecl("r", typeVar)()),
    domainType
  )(domainName = domainName)

  /**
   * {{{
   *   function ssecond(r: T): Int
   * }}}
   */
  private lazy val ssecond_func: vpr.DomainFunc = vpr.DomainFunc(
    "ssecond",
    Seq(vpr.LocalVarDecl("r", typeVar)()),
    vpr.Int
  )(domainName = domainName)

  /**
    * {{{
    * axiom slice_offset_nonneg {
    *   forall s : Slice[T] :: { soffset(s) } 0 <= soffset(s)
    * }
    * }}}
    */
    /*
  private lazy val slice_offset_nonneg_axiom : vpr.DomainAxiom = {
    val sDecl = vpr.LocalVarDecl("s", domainType)()
    val exp = offset(sDecl.localVar)()

    vpr.AnonymousDomainAxiom(
      vpr.Forall(
        Seq(sDecl),
        Seq(vpr.Trigger(Seq(exp))()),
        vpr.LeCmp(vpr.IntLit(0)(), exp)()
      )()
    )(domainName = domainName)
  }

     */

  /**
    * {{{
    * axiom slice_len_nonneg {
    *   forall s : Slice[T] :: { slen(s) } 0 <= slen(s)
    * }
    * }}}
    */
  private lazy val slice_len_nonneg_axiom : vpr.DomainAxiom = {
    val sDecl = vpr.LocalVarDecl("s", domainType)()
    val exp = len(sDecl.localVar)()

    vpr.AnonymousDomainAxiom(
      vpr.Forall(
        Seq(sDecl),
        Seq(vpr.Trigger(Seq(exp))()),
        vpr.LeCmp(vpr.IntLit(0)(), exp)()
      )()
    )(domainName = domainName)
  }

  /**
    * {{{
    * axiom slice_len_leq_cap {
    *   forall s : Slice[T] :: { slen(s) } { scap(s) } slen(s) <= scap(s)
    * }
    * }}}
    */
  private lazy val slice_len_leq_cap_axiom : vpr.DomainAxiom = {
    val sDecl = vpr.LocalVarDecl("s", domainType)()
    val left = len(sDecl.localVar)()
    val right = cap(sDecl.localVar)()

    vpr.AnonymousDomainAxiom(
      vpr.Forall(
        Seq(sDecl),
        Seq(vpr.Trigger(Seq(left))(), vpr.Trigger(Seq(right))()),
        vpr.LeCmp(left, right)()
      )()
    )(domainName = domainName)
  }

  /**
    * {{{
    * axiom slice_cap_leq_alen {
    *   forall s : Slice[T] :: { soffset(s), scap(s) } { alen(sarray(s)) }
    *     soffset(s) + scap(s) <= alen(sarray(s))
    * }
    * }}}
    */
    /*
  private lazy val slice_cap_leq_alen_axiom : vpr.DomainAxiom = {
    val sDecl = vpr.LocalVarDecl("s", domainType)()
    val soffset = offset(sDecl.localVar)()
    val scap = cap(sDecl.localVar)()
    val alen = arrays.len(array(sDecl.localVar)())()

    vpr.AnonymousDomainAxiom(
      vpr.Forall(
        Seq(sDecl),
        Seq(vpr.Trigger(Seq(soffset, scap))(), vpr.Trigger(Seq(alen))()),
        vpr.LeCmp(vpr.Add(soffset, scap)(), alen)()
      )()
    )(domainName = domainName)
  }

     */

  /**
    * {{{
    * axiom slice_deconstructor_over_constructor_array {
    *   forall arr, off, len, cap :: { sarray(smake(arr,off,len,cap)) }
    *     0 <= off && 0 <= len && len <= cap && off + cap <= alen(arr) ==> sarray(smake(arr,off,len,cap)) == arr
    * }
    *
    * axiom slice_deconstructor_over_constructor_offset {
    *   forall arr, off, len, cap :: { soffset(smake(arr,off,len,cap)) }
    *     0 <= off && 0 <= len && len <= cap && off + cap <= alen(arr) ==> soffset(smake(arr,off,len,cap)) == off
    * }
    *
    * axiom slice_deconstructor_over_constructor_len {
    *   forall arr, off, len, cap :: { slen(smake(arr,off,len,cap)) }
    *     0 <= off && 0 <= len && len <= cap && off + cap <= alen(arr) ==> slen(smake(arr,off,len,cap)) == len
    * }
    *
    * axiom slice_deconstructor_over_constructor_cap {
    *   forall arr, off, len, cap :: { slen(smake(arr,off,len,cap)) }
    *     0 <= off && 0 <= len && len <= cap && off + cap <= alen(arr) ==> scap(smake(arr,off,len,cap)) == cap
    * }
    * }}}
    */
  private lazy val slice_deconstructors_over_constructor: Vector[vpr.DomainAxiom] = {
    val lehDecl = vpr.LocalVarDecl("l", vpr.Int)(); val leh = lehDecl.localVar
    val cayDecl = vpr.LocalVarDecl("c", vpr.Int)(); val cay = cayDecl.localVar

    val smake = make(leh,cay)()
    val lhs = vpr.And(
        vpr.LeCmp(vpr.IntLit(0)(), leh)(), vpr.LeCmp(leh, cay)())()

    val funcAppAxiom3 = len(smake)()
    val funcAppAxiom4 = cap(smake)()
    val rhsAxiom3 = vpr.EqCmp(funcAppAxiom3, leh)()
    val rhsAxiom4 = vpr.EqCmp(funcAppAxiom4, cay)()

    val axiom3 = vpr.NamedDomainAxiom(
      "deconstructor_over_constructor_len",
      vpr.Forall(
        Seq(lehDecl, cayDecl),
        Seq(vpr.Trigger(Seq(funcAppAxiom3))()),
        vpr.Implies(lhs, rhsAxiom3)()
      )()
    )(domainName = domainName)
    val axiom4 = vpr.NamedDomainAxiom(
      "deconstructor_over_constructor_cap",
      vpr.Forall(
        Seq(lehDecl, cayDecl),
        Seq(vpr.Trigger(Seq(funcAppAxiom4))()),
        vpr.Implies(lhs, rhsAxiom4)()
      )()
    )(domainName = domainName)

    Vector(axiom3, axiom4)
  }

  /**
    * {{{
    * axiom slice_constructor_over_deconstructor {
    *   forall s :: { slen(s) }{ scap(s) }
    *     s == smake(slen(s), scap(s))
    * }
    * }}}
    */
  private lazy val slice_constructor_over_deconstructor : vpr.DomainAxiom = {
    val sDecl = vpr.LocalVarDecl("s", domainType)(); val s = sDecl.localVar

    val slen = len(s)()
    val scap = cap(s)()

    vpr.AnonymousDomainAxiom(
      vpr.Forall(
        Seq(sDecl),
        Seq(vpr.Trigger(Seq(slen))(), vpr.Trigger(Seq(scap))()),
        vpr.EqCmp(s, make(slen, scap)())()
      )()
    )(domainName = domainName)
  }

  /**
   * {{{
   *   axiom {
   *     (forall s: Slice[T], i: Int :: { (sloc(s, i): T) }
   *        0 <= i && i < (slen(s): Int) ==>
   *        (sfirst((sloc(s, i): T)): Slice[T]) == s &&
   *        (ssecond((sloc(s, i): T)): Int) == i)
   *      }
   * }}}
   */
  private lazy val sfirst_and_ssecond: vpr.DomainAxiom = {
    val sDecl = vpr.LocalVarDecl("s", domainType)();
    val iDecl = vpr.LocalVarDecl("i", vpr.Int)();
    val i = iDecl.localVar
    val s = sDecl.localVar

    val sloc = loc(s, i)()

    vpr.AnonymousDomainAxiom(
      vpr.Forall(
        Seq(sDecl, iDecl),
        Seq(vpr.Trigger(Seq(sloc))()),
        vpr.And(
          vpr.EqCmp(first(sloc)(), s)(),
          vpr.EqCmp(second(sloc)(), i)())()
      )()
    )(domainName = domainName)
  }


  /**
    * Definition of the following auxiliary Viper function,
    * used to improve verification with the `loc` function:
    *
    * {{{
    * function sadd(left: Int, right: Int): Int
    *   ensures result == left + right
    * {
    *   left + right
    * }
    * }}}
    */
  private def sadd_func_def() : vpr.Function = {
    val lDecl = vpr.LocalVarDecl("left", vpr.Int)()
    val rDecl = vpr.LocalVarDecl("right", vpr.Int)()
    val body : vpr.Exp = vpr.Add(lDecl.localVar, rDecl.localVar)()
    val post : vpr.Exp = vpr.EqCmp(vpr.Result(vpr.Int)(), body)()
    vpr.Function("sadd", Seq(lDecl, rDecl), vpr.Int, Seq(), Seq(post), Some(body))()
  }

  /**
    * {{{
    * domain Slice[T] {
    *   function slen(s : Slice[T]) : Int
    *   function scap(s : Slice[T]) : Int
    *
    *   axiom slice_offset_nonneg {
    *     forall s : Slice[T] :: { soffset(s) } 0 <= soffset(s)
    *   }
    *
    *   axiom slice_len_nonneg {
    *     forall s : Slice[T] :: { slen(s) } 0 <= slen(s)
    *   }
    *
    *   axiom slice_len_leq_cap {
    *     forall s : Slice[T] :: { slen(s) } { scap(s) } slen(s) <= scap(s)
    *   }
    *
    *   axiom slice_cap_leq_alen {
    *     forall s : Slice[T] :: { soffset(s), scap(s) } { alen(sarray(s)) }
    *       soffset(s) + scap(s) <= alen(sarray(s))
    *   }
    *
    *   axiom slice_deconstructor_over_constructor_array {
    *     forall arr, off, len, cap :: { sarray(smake(arr,off,len,cap)) }
    *       0 <= off && 0 <= len && len <= cap && off + cap <= alen(arr) ==> sarray(smake(arr,off,len,cap)) == arr
    *   }
    *
    *   axiom slice_deconstructor_over_constructor_offset {
    *     forall arr, off, len, cap :: { soffset(smake(arr,off,len,cap)) }
    *       0 <= off && 0 <= len && len <= cap && off + cap <= alen(arr) ==> soffset(smake(arr,off,len,cap)) == off
    *   }
    *
    *   axiom slice_deconstructor_over_constructor_len {
    *     forall arr, off, len, cap :: { slen(smake(arr,off,len,cap)) }
    *       0 <= off && 0 <= len && len <= cap && off + cap <= alen(arr) ==> slen(smake(arr,off,len,cap)) == len
    *   }
    *
    *   axiom slice_deconstructor_over_constructor_cap {
    *     forall arr, off, len, cap :: { slen(smake(arr,off,len,cap)) }
    *       0 <= off && 0 <= len && len <= cap && off + cap <= alen(arr) ==> scap(smake(arr,off,len,cap)) == cap
    *   }
    *
    *   axiom slice_constructor_over_deconstructor {
    *     forall s :: { sarray(s) }{ soffset(s) }{ slen(s) }{ scap(s) }
    *       s == smake(sarray(s), soffset(s), slen(s), scap(s))
    *   }
    * }
    * }}}
    */
  private lazy val domain : vpr.Domain = vpr.Domain(
    domainName,
    Seq(slen_func, scap_func, sloc_func, smake_func, sfirst_func, ssecond_func),
      slice_len_nonneg_axiom +:
      slice_len_leq_cap_axiom +:
      sfirst_and_ssecond +:
      slice_constructor_over_deconstructor +:
      slice_deconstructors_over_constructor,
    Seq(typeVar)
  )()

  /** A function application of "sadd". */
  private def add(left : vpr.Exp, right : vpr.Exp)(pos : vpr.Position, info : vpr.Info, errT : vpr.ErrorTrafo) : vpr.FuncApp = {
    generateDomain = true
    vpr.FuncApp(sadd_func.name, Seq(left, right))(pos, info, vpr.Int, errT)
  }

  /** A function application of "sarray". */
  override def array(exp : vpr.Exp)(pos : vpr.Position, info : vpr.Info, errT : vpr.ErrorTrafo) : vpr.DomainFuncApp = {
    generateDomain = true
    vpr.DomainFuncApp(
      func = sarray_func,
      args = Vector(exp),
      typVarMap = exp.typ.asInstanceOf[vpr.DomainType].typVarsMap
    )(pos, info, errT)
  }

  /** A function application of "scap". */
  override def cap(exp : vpr.Exp)(pos : vpr.Position, info : vpr.Info, errT : vpr.ErrorTrafo) : vpr.DomainFuncApp = {
    generateDomain = true
    vpr.DomainFuncApp(
      func = scap_func,
      args = Vector(exp),
      typVarMap = exp.typ.asInstanceOf[vpr.DomainType].typVarsMap
    )(pos, info, errT)
  }

  /** A function application of "slen". */
  override def len(exp : vpr.Exp)(pos : vpr.Position, info : vpr.Info, errT : vpr.ErrorTrafo) : vpr.DomainFuncApp = {
    generateDomain = true
    vpr.DomainFuncApp(
      func = slen_func,
      args = Vector(exp),
      typVarMap = exp.typ.asInstanceOf[vpr.DomainType].typVarsMap
    )(pos, info, errT)
  }

  /** A function application of "soffset". */
  override def offset(exp : vpr.Exp)(pos : vpr.Position, info : vpr.Info, errT : vpr.ErrorTrafo) : vpr.DomainFuncApp = {
    generateDomain = true
    vpr.DomainFuncApp(
      func = soffset_func,
      args = Vector(exp),
      typVarMap = exp.typ.asInstanceOf[vpr.DomainType].typVarsMap
    )(pos, info, errT)
  }

  /**
    * A function application of the "sloc" function.
    */
  override def loc(base : vpr.Exp, index : vpr.Exp)(pos : vpr.Position, info : vpr.Info, errT : vpr.ErrorTrafo) : vpr.Exp = {
    generateDomain = true
    vpr.DomainFuncApp(
      func = sloc_func,
      args = Seq(base, index),
      typVarMap = base.typ.asInstanceOf[vpr.DomainType].typVarsMap
    )(pos, info, errT)
  }

  /** A function application of "smake". */
  def make(len: vpr.Exp, cap: vpr.Exp)(pos: vpr.Position = vpr.NoPosition, info: vpr.Info = vpr.NoInfo, errT: vpr.ErrorTrafo = vpr.NoTrafos) : vpr.DomainFuncApp = {
    generateDomain = true
    vpr.DomainFuncApp(
      func = smake_func,
      args = Vector(len, cap),
      typVarMap = domainType.typVarsMap
    )(pos, info, errT)
  }

  /** A function application of "sfirst". */
  def first(r: vpr.Exp)(pos: vpr.Position = vpr.NoPosition, info: vpr.Info = vpr.NoInfo, errT: vpr.ErrorTrafo = vpr.NoTrafos) : vpr.DomainFuncApp = {
    generateDomain = true
    val typeVar = vpr.TypeVar("T")
    val typeVarMap = Map(typeVar -> typeVar)
    vpr.DomainFuncApp(
      func = sfirst_func,
      args = Vector(r),
      typVarMap = typeVarMap
    )(pos, info, errT)
  }

  /** A function application of "ssecond". */
  def second(r: vpr.Exp)(pos: vpr.Position = vpr.NoPosition, info: vpr.Info = vpr.NoInfo, errT: vpr.ErrorTrafo = vpr.NoTrafos): vpr.DomainFuncApp = {
    generateDomain = true
    val typeVar = vpr.TypeVar("T")
    val typeVarMap = Map(typeVar -> typeVar)
    vpr.DomainFuncApp(
      func = ssecond_func,
      args = Vector(r),
      typVarMap = typeVarMap
    )(pos, info, errT)
  }

  /** Yields the Viper domain type of slices. */
  def typ(t : vpr.Type) : vpr.DomainType = {
    generateDomain = true
    vpr.DomainType(domain, Map(typeVar -> t))
  }

  override def finalize(addMemberFn: vpr.Member => Unit) : Unit = {
    if (generateDomain) {
      addMemberFn(domain)
      // addMemberFn(sadd_func)
    }
  }
}
