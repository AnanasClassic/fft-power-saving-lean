import Submission.Chain.Schedule
import Mathlib.Data.List.Sort
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Fintype.Fin

namespace FFTChainDFT.Chain.Schedule
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

/-- Tag zero denotes one whole native invocation; the other tags denote
one thin query or one whole idle on every one of the 104 native ports. -/
def billTag : Op → List ℕ
  | .full _ _ _ => [0]
  | .query _ _ => [1]
  | .idle _ ks => [8*ks.length]
  | _ => []
def tags : List ℕ := code.flatMap billTag
def expectedTags : List ℕ := List.replicate 36 0 ++ List.replicate 6 1 ++
  (List.range 8).flatMap (fun j => List.replicate 4 (8*(j+1)))
theorem tags_sorted : List.insertionSort (·≤·) tags = List.insertionSort (·≤·) expectedTags := by
  decide +kernel

theorem tags_perm : List.Perm tags expectedTags := by
  have h := (List.perm_insertionSort (·≤·) tags).symm
  rw [tags_sorted] at h
  exact h.trans (List.perm_insertionSort (·≤·) expectedTags)

def nativeTrace : List (ℕ × ℕ × ℕ) := code.filterMap fun op =>
  match op with
  | .full k a b => some (k.val,a.val,b.val)
  | _ => none

theorem native_trace : nativeTrace = (List.range 18).flatMap (fun j => [(j,1,0),(j,21,20)]) := by
  decide +kernel

def nativeIDs : List ℕ := nativeTrace.map fun (k,a,_) => 2*k+a/20
theorem native_ids : nativeIDs = List.range 36 := by decide +kernel
 theorem native_unique : nativeIDs.Nodup := by rw [native_ids]; exact List.nodup_range

def queryTrace : List (ℕ × ℕ) := code.filterMap fun op =>
  match op with
  | .query a b => some (a.val,b.val)
  | _ => none
 theorem queries_exact : queryTrace = [(0,1),(20,21),(0,1),(20,21),(0,1),(20,21)] := by
  decide +kernel

/-- The literal schedule's bill, for any additive cost interpretation. -/
theorem tag_sum {R : Type*} [AddCommMonoid R] (v : ℕ → R) :
    (tags.map v).sum = 36 • v 0 + 6 • v 1 +
      ((List.range 8).map fun j => 4 • v (8*(j+1))).sum := by
  rw [(tags_perm.map v).sum_eq]
  have hflat (l : List ℕ) :
      ((l.flatMap fun j => List.replicate 4 (8*(j+1))).map v).sum =
        (l.map fun j => 4 • v (8*(j+1))).sum := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.map_replicate, List.sum_replicate, List.map_cons, List.sum_cons, ih]
  simp only [expectedTags, List.map_append, List.sum_append,
    List.map_replicate, List.sum_replicate, hflat, add_assoc]
end FFTChainDFT.Chain.Schedule
#print axioms FFTChainDFT.Chain.Schedule.native_trace
#print axioms FFTChainDFT.Chain.Schedule.tag_sum
