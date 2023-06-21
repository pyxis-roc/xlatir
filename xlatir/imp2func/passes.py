#!/usr/bin/env python3
#
# passes.py
# A list of all passes collected in one place, use as 'from xlatir.imp2func.passes import *'.
#
# SPDX-FileCopyrightText: 2020,2021,2023 University of Rochester
#
# SPDX-License-Identifier: MIT

from .imp2func_ssa import XIRFileLoaderPass, AnnotationsPass, PrologueOutputPass, BackendOutputPass, InitBackendPass, TypesFilePass, InlineTypesPass, SetStdOutPass, ConvertSSAToFunctionalPass
from .passmgr import PhasePass
from .impdfanalysis import CFGBuilderPass, CFGIdentifyNonExitingPass, CFGHandleNonExitingPass, CFGMergeBranchExitNodesPass, CFGDumperPass, CFGUnreachableNodesPass
from .impssa import SSAPlacePhiPass, SSABranchesToFunctionsPass, SSARenameVariablesPass, assemble_convert_to_SSA

#deprecated: CFGStructureCheckerPass, CFGNonExitingPrunePass
