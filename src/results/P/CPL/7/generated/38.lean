

theorem P2_of_closed_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed A) (h_dense : closure A = Set.univ) : Topology.P2 A := by
  -- A closed dense set must be the whole space.
  have hA_univ : (A : Set X) = Set.univ := by
    simpa [hA_closed.closure_eq] using h_dense
  -- `P2` holds for `Set.univ`; transport this fact to `A`.
  simpa [hA_univ] using (P2_univ : Topology.P2 (Set.univ : Set X))

theorem P1_of_P3_and_closed {X : Type*} [TopologicalSpace X] {A : Set X} (h_closed : IsClosed A) (hP3 : Topology.P3 A) : Topology.P1 A := by
  intro x hxA
  -- Use `P3` to place `x` inside `interior (closure A)`,
  -- then rewrite with the fact that `A` is closed.
  have hx_int : x ∈ interior (A : Set X) := by
    have : x ∈ interior (closure (A : Set X)) := hP3 hxA
    simpa [h_closed.closure_eq] using this
  -- The closure contains its interior.
  exact subset_closure hx_int

theorem P1_prod_prod {X₁ : Type*} [TopologicalSpace X₁] {X₂ : Type*} [TopologicalSpace X₂] {Y₁ : Type*} [TopologicalSpace Y₁] {Y₂ : Type*} [TopologicalSpace Y₂] {A : Set X₁} {B : Set X₂} {C : Set Y₁} {D : Set Y₂} (h1 : Topology.P1 A) (h2 : Topology.P1 B) (h3 : Topology.P1 C) (h4 : Topology.P1 D) : Topology.P1 ((A ×ˢ B) ×ˢ (C ×ˢ D)) := by
  have hAB : Topology.P1 (A ×ˢ B) := P1_prod h1 h2
  have hCD : Topology.P1 (C ×ˢ D) := P1_prod h3 h4
  simpa using P1_prod hAB hCD

theorem P2_prod_univ_rev {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y] {A : Set Y} (hA : Topology.P2 A) : Topology.P2 ((Set.univ : Set X) ×ˢ A) := by
  have hUniv : Topology.P2 (Set.univ : Set X) := P2_univ
  simpa using (P2_prod (A := (Set.univ : Set X)) (B := A) hUniv hA)

theorem P3_prod_univ_rev {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y] {A : Set Y} (hA : Topology.P3 A) : Topology.P3 ((Set.univ : Set X) ×ˢ A) := by
  have hUniv : Topology.P3 (Set.univ : Set X) := P3_univ
  simpa using (P3_prod (A := (Set.univ : Set X)) (B := A) hUniv hA)

theorem exists_open_subset_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.P2 A) : ∃ U, IsOpen U ∧ A ⊆ closure U ∧ U ⊆ closure (interior A) := by
  refine ⟨interior (closure (interior A)), isOpen_interior, ?_, ?_⟩
  · intro x hx
    exact subset_closure (hA hx)
  ·
    exact interior_subset