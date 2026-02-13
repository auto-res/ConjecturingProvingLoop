

theorem interior_closure_eq_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → interior (closure A) = interior (closure (interior A)) := by
  intro hP2
  -- `P2 A` implies `P1 A`
  have hP1 : P1 A := P2_to_P1 (A := A) hP2
  -- hence the two closures coincide
  have hClosureEq : closure (interior A : Set X) = closure A :=
    closure_interior_eq_of_P1 (A := A) hP1
  -- rewriting with this equality finishes the proof
  simpa [hClosureEq]

theorem P1_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} : interior A = Set.univ → P1 A := by
  intro hIntUniv
  exact P2_to_P1 (A := A) ((P2_of_dense_interior (A := A)) hIntUniv)