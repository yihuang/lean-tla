import Leslie.Examples.CacheCoherence.TileLink.Types

/-! ## TileLink Permission Helpers

    Permission-level helper functions and small algebraic lemmas used by later
    TileLink models and invariants.
-/

namespace TileLink

def TLPerm.isCached : TLPerm → Prop
  | .N => False
  | .B => True
  | .T => True

def TLPerm.allowsRead : TLPerm → Prop
  | .N => False
  | .B => True
  | .T => True

def TLPerm.allowsWrite : TLPerm → Prop
  | .N => False
  | .B => False
  | .T => True

def TLPerm.mayBeDirty : TLPerm → Prop
  | .N => False
  | .B => False
  | .T => True

theorem TLPerm.isCached_iff_ne_N (perm : TLPerm) :
    perm.isCached ↔ perm ≠ .N := by
  cases perm <;> simp [TLPerm.isCached]

theorem TLPerm.allowsRead_iff_isCached (perm : TLPerm) :
    perm.allowsRead ↔ perm.isCached := by
  cases perm <;> simp [TLPerm.allowsRead, TLPerm.isCached]

theorem TLPerm.allowsWrite_iff_eq_T (perm : TLPerm) :
    perm.allowsWrite ↔ perm = .T := by
  cases perm <;> simp [TLPerm.allowsWrite]

theorem TLPerm.mayBeDirty_iff_eq_T (perm : TLPerm) :
    perm.mayBeDirty ↔ perm = .T := by
  cases perm <;> simp [TLPerm.mayBeDirty]

theorem TLPerm.mayBeDirty_implies_allowsWrite {perm : TLPerm} :
    perm.mayBeDirty → perm.allowsWrite := by
  cases perm <;> simp [TLPerm.mayBeDirty, TLPerm.allowsWrite]

theorem TLPerm.allowsWrite_implies_allowsRead {perm : TLPerm} :
    perm.allowsWrite → perm.allowsRead := by
  cases perm <;> simp [TLPerm.allowsWrite, TLPerm.allowsRead]

def GrowParam.source : GrowParam → TLPerm
  | .NtoB => .N
  | .NtoT => .N
  | .BtoT => .B

def GrowParam.result : GrowParam → TLPerm
  | .NtoB => .B
  | .NtoT => .T
  | .BtoT => .T

def GrowParam.legalFrom (grow : GrowParam) (perm : TLPerm) : Prop :=
  perm = grow.source

theorem GrowParam.result_cached (grow : GrowParam) :
    grow.result.isCached := by
  cases grow <;> simp [GrowParam.result, TLPerm.isCached]

theorem GrowParam.result_allowsRead (grow : GrowParam) :
    grow.result.allowsRead := by
  cases grow <;> simp [GrowParam.result, TLPerm.allowsRead]

theorem GrowParam.result_allowsWrite_iff (grow : GrowParam) :
    grow.result.allowsWrite ↔ grow ≠ .NtoB := by
  cases grow <;> simp [GrowParam.result, TLPerm.allowsWrite]

def CapParam.result : CapParam → TLPerm
  | .toT => .T
  | .toB => .B
  | .toN => .N

def CapParam.legalFrom (cap : CapParam) (perm : TLPerm) : Prop :=
  match cap, perm with
  | .toT, .T => True
  | .toB, .T => True
  | .toB, .B => True
  | .toN, _ => True
  | _, _ => False

theorem CapParam.result_read_iff (cap : CapParam) :
    cap.result.allowsRead ↔ cap ≠ .toN := by
  cases cap <;> simp [CapParam.result, TLPerm.allowsRead]

theorem CapParam.result_write_iff (cap : CapParam) :
    cap.result.allowsWrite ↔ cap = .toT := by
  cases cap <;> simp [CapParam.result, TLPerm.allowsWrite]

def PruneReportParam.source : PruneReportParam → TLPerm
  | .TtoB => .T
  | .TtoN => .T
  | .BtoN => .B
  | .TtoT => .T
  | .BtoB => .B
  | .NtoN => .N

def PruneReportParam.result : PruneReportParam → TLPerm
  | .TtoB => .B
  | .TtoN => .N
  | .BtoN => .N
  | .TtoT => .T
  | .BtoB => .B
  | .NtoN => .N

def PruneReportParam.isPrune : PruneReportParam → Prop
  | .TtoB => True
  | .TtoN => True
  | .BtoN => True
  | .TtoT => False
  | .BtoB => False
  | .NtoN => False

def PruneReportParam.isReport : PruneReportParam → Prop
  | .TtoB => False
  | .TtoN => False
  | .BtoN => False
  | .TtoT => True
  | .BtoB => True
  | .NtoN => True

def PruneReportParam.legalFrom (param : PruneReportParam) (perm : TLPerm) : Prop :=
  perm = param.source

theorem PruneReportParam.isPrune_iff_source_ne_result (param : PruneReportParam) :
    param.isPrune ↔ param.source ≠ param.result := by
  cases param <;> simp [PruneReportParam.isPrune, PruneReportParam.source, PruneReportParam.result]

theorem PruneReportParam.isReport_iff_source_eq_result (param : PruneReportParam) :
    param.isReport ↔ param.source = param.result := by
  cases param <;> simp [PruneReportParam.isReport, PruneReportParam.source, PruneReportParam.result]

theorem PruneReportParam.result_read_implies_source_read {param : PruneReportParam} :
    param.result.allowsRead → param.source.allowsRead := by
  cases param <;> simp [PruneReportParam.result, PruneReportParam.source, TLPerm.allowsRead]

theorem PruneReportParam.result_write_implies_source_write {param : PruneReportParam} :
    param.result.allowsWrite → param.source.allowsWrite := by
  cases param <;> simp [PruneReportParam.result, PruneReportParam.source, TLPerm.allowsWrite]

end TileLink
