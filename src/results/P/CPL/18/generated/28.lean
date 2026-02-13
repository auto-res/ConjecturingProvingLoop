

theorem P3_prod_four {W X Y Z : Type*} [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set W} {B : Set X} {C : Set Y} {D : Set Z} (hA : Topology.P3 A) (hB : Topology.P3 B) (hC : Topology.P3 C) (hD : Topology.P3 D) : Topology.P3 (((A.prod B).prod C).prod D) := by
  -- First, obtain `P3` for `A × B`.
  have hAB : Topology.P3 (A.prod B) :=
    P3_prod (X := W) (Y := X) (A := A) (B := B) hA hB
  -- Then, obtain `P3` for `(A × B) × C`.
  have hABC : Topology.P3 ((A.prod B).prod C) :=
    P3_prod
      (X := W × X) (Y := Y)
      (A := (A.prod B)) (B := C) hAB hC
  -- Finally, combine this set with `D`.
  have hABCD : Topology.P3 (((A.prod B).prod C).prod D) :=
    P3_prod
      (X := (W × X) × Y) (Y := Z)
      (A := ((A.prod B).prod C)) (B := D) hABC hD
  simpa using hABCD

theorem P1_closure_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P1 A) (hB : Topology.P1 B) : Topology.P1 (closure A ∪ closure B) := by
  -- First, upgrade the hypotheses to the closures.
  have hA_cl : Topology.P1 (closure A) := P1_closure (X := X) (A := A) hA
  have hB_cl : Topology.P1 (closure B) := P1_closure (X := X) (A := B) hB
  -- Then apply the union lemma.
  have h_union : Topology.P1 (closure A ∪ closure B) :=
    P1_union (A := closure A) (B := closure B) hA_cl hB_cl
  simpa using h_union

theorem exists_P3_dense_subset {X : Type*} [TopologicalSpace X] : ∃ A : Set X, Dense A ∧ Topology.P3 A := by
  refine ⟨(Set.univ : Set X), dense_univ, ?_⟩
  simpa using (P3_univ (X := X))