

theorem P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.P1 A) : Topology.P1 (closure A) := by
  dsimp [Topology.P1] at hA ⊢
  intro x hx_closureA
  -- Using `P1 A`, we know `closure (interior A) = closure A`.
  have h_eq := closure_eq_of_P1 hA
  -- Rewrite `hx_closureA` so that it lies in `closure (interior A)`.
  have hx_closure_intA : x ∈ closure (interior A) := by
    simpa [h_eq] using hx_closureA
  -- `interior A ⊆ interior (closure A)`
  have h_interior_subset : interior A ⊆ interior (closure A) :=
    interior_mono (subset_closure)
  -- Taking closures preserves the inclusion.
  have h_closure_subset :
      closure (interior A) ⊆ closure (interior (closure A)) :=
    closure_mono h_interior_subset
  -- Conclude.
  exact h_closure_subset hx_closure_intA

theorem P1_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : Topology.P1 A) : Topology.P1 (Set.prod A (Set.univ : Set Y)) := by
  have h_univ : Topology.P1 (Set.univ : Set Y) := by
    exact Topology.P1_of_open (A := (Set.univ : Set Y)) isOpen_univ
  simpa using Topology.P1_prod hA h_univ

theorem P2_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : Topology.P2 A) : Topology.P2 (Set.prod A (Set.univ : Set Y)) := by
  have h_univ : Topology.P2 (Set.univ : Set Y) := Topology.P2_univ (X := Y)
  simpa using
    (Topology.P2_prod (A := A) (B := (Set.univ : Set Y)) hA h_univ)

theorem P3_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : Topology.P3 A) : Topology.P3 (Set.prod A (Set.univ : Set Y)) := by
  have h_univ : Topology.P3 (Set.univ : Set Y) := Topology.P3_univ (X := Y)
  simpa using
    (Topology.P3_prod (A := A) (B := (Set.univ : Set Y)) hA h_univ)