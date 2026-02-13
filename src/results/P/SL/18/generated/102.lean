

theorem dense_closure_iff_dense {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (closure (A : Set X)) ↔ Dense (A : Set X) := by
  classical
  constructor
  · intro hDenseClos
    -- Translate density of `closure A` into a closure equality.
    have hEq₁ : closure (closure (A : Set X)) = (Set.univ : Set X) :=
      (Topology.dense_iff_closure_eq_univ).1 hDenseClos
    -- Use `closure_closure` to rewrite.
    have hEq₂ : closure (A : Set X) = (Set.univ : Set X) := by
      simpa [closure_closure] using hEq₁
    -- Re‐encode as density of `A`.
    exact (Topology.dense_iff_closure_eq_univ).2 hEq₂
  · intro hDenseA
    -- Translate density of `A` into a closure equality.
    have hEq₁ : closure (A : Set X) = (Set.univ : Set X) :=
      (Topology.dense_iff_closure_eq_univ).1 hDenseA
    -- Apply `closure_closure` to obtain the desired equality.
    have hEq₂ : closure (closure (A : Set X)) = (Set.univ : Set X) := by
      simpa [closure_closure] using hEq₁
    -- Re‐encode as density of `closure A`.
    exact (Topology.dense_iff_closure_eq_univ).2 hEq₂