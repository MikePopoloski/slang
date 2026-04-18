// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT

// Without --allow-lib-module-redef, a module and a primitive sharing the same
// name produce a hard Redefinition error.
// RUN: %slang --single-unit %data/redef_module.sv %data/redef_primitive.sv %data/redef_top.sv 2>&1 || true
// CHECK: redefinition of 'mux_primitive'

// With --allow-lib-module-redef and both conflicting files as library files,
// the first definition wins and the conflict is silently discarded.
// RUN: %slang --single-unit --allow-lib-module-redef -v %data/redef_module.sv -v %data/redef_primitive.sv %data/redef_top.sv 2>&1
// CHECK: Build succeeded

// With --allow-lib-module-redef but files NOT specified as libraries,
// redefinition is still an error.
// RUN: %slang --single-unit --allow-lib-module-redef %data/redef_module.sv %data/redef_primitive.sv %data/redef_top.sv 2>&1 || true
// CHECK: redefinition of 'mux_primitive'

// --compat=vcs should automatically enable --allow-lib-module-redef.
// RUN: %slang --single-unit --compat=vcs -v %data/redef_module.sv -v %data/redef_primitive.sv %data/redef_top.sv 2>&1
// CHECK: Build succeeded
