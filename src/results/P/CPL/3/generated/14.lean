

theorem P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} : closure (interior A) = (Set.univ : Set X) → P3 A := by
  intro h_dense
  exact P2_subset_P3 (P2_of_dense_interior h_dense)

theorem P2_of_P1_and_open_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → IsOpen (closure A) → P2 A := by
  intro hP1 h_open
  -- First, build `P3 A` using the fact that `closure A` is open.
  have hP3 : P3 A := by
    intro x hxA
    have hx_closure : x ∈ closure A := subset_closure hxA
    simpa [h_open.interior_eq] using hx_closure
  -- Combine `hP1` and `hP3` via the equivalence to obtain `P2 A`.
  exact (P2_iff_P1_and_P3).2 ⟨hP1, hP3⟩