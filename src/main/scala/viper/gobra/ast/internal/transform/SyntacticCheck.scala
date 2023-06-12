// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.gobra.ast.internal.transform

import viper.gobra.ast.{internal => in}
import viper.gobra.translator.Names
import viper.gobra.util.Violation

/**
  * Transformation responsible for generating call-graph edges from interface methods to their implementations' methods.
  * This is necessary to soundly verify termination in the presence of dynamic method binding.
  */
object SyntacticCheck extends InternalTransform {
  override def name(): String = "syntactic_check_for_slices"

  /**
    * Program-to-program transformation
    */
  override def transform(p: in.Program): in.Program = {
    in.Program(
      types = p.types,
      members = p.members,
      table = p.table,
    )(p.info)
  }
}
