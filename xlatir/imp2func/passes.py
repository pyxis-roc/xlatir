#!/usr/bin/env python3
#
# passes.py
# A list of all passes collected in one place, use as 'from xlatir.imp2func.passes import *'.

from .imp2func_ssa import XIRFileLoaderPass, AnnotationsPass, PrologueOutputPass, BackendOutputPass, InitBackendPass, TypesFilePass, InlineTypesPass, SetStdOutPass
from .passmgr import PhasePass
from .impdfanalysis import CFGBuilderPass, CFGIdentifyNonExitingPass, CFGHandleNonExitingPass, CFGMergeBranchExitNodesPass, CFGDumperPass, CFGUnreachableNodesPass

#deprecated: CFGStructureCheckerPass, CFGNonExitingPrunePass
