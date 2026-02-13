

theorem P1_dense_subset {X : Type*} [TopologicalSpace X] {A B : Set X} : A ⊆ B → closure A = closure B → P1 A → P1 B := by
  intro hAB hClos hP1
  intro x hxB
  -- Step 1: `x` lies in `closure A` (via the equality of closures).
  have hx_clA : x ∈ closure A := by
    have : x ∈ closure B := subset_closure hxB
    simpa [hClos] using this
  -- Step 2: `closure (interior A) = closure A` (from `P1 A`).
  have h_cl_eq : closure (interior A) = closure A :=
    (P1_iff_closure_eq (A := A)).1 hP1
  have hx_cl_intA : x ∈ closure (interior A) := by
    simpa [h_cl_eq] using hx_clA
  -- Step 3: `closure (interior A) ⊆ closure (interior B)` (since `A ⊆ B`).
  have hx_cl_intB : x ∈ closure (interior B) := by
    have h_subset : closure (interior A) ⊆ closure (interior B) := by
      exact closure_mono (interior_mono hAB)
    exact h_subset hx_cl_intA
  exact hx_cl_intB

theorem P3_interior_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P3 (interior A) := by
  intro hP2
  have hP2Int : P2 (interior A) := P2_interior (A := A) hP2
  exact (P2_subset_P3 (A := interior A) hP2Int)