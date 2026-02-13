

theorem P2_univ {X : Type*} [TopologicalSpace X] : Topology.P2 (Set.univ : Set X) := by
  dsimp [Topology.P2]
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P1_iff_P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P1 A ↔ Topology.P2 A := by
  constructor
  · intro _hP1
    exact Topology.P2_of_open (A := A) hA
  · intro hP2
    exact Topology.P2_implies_P1 hP2

theorem P2_iff_P3_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P2 A ↔ Topology.P3 A := by
  constructor
  ·
    exact Topology.P2_implies_P3
  ·
    intro hP3
    dsimp [Topology.P2] at *
    intro x hxA
    -- From `P3` and the fact that `A` is closed, we get `x ∈ interior A`.
    have hx_intA : x ∈ interior A := by
      have : x ∈ interior (closure A) := hP3 hxA
      simpa [hA.closure_eq] using this
    -- We now show that `interior A ⊆ interior (closure (interior A))`.
    have h_subset : interior A ⊆ interior (closure (interior A)) := by
      -- First, `interior A` is contained in its closure.
      have h_cl : interior A ⊆ closure (interior A) := by
        intro y hy
        exact subset_closure hy
      -- Apply `interior_maximal`; note `interior (interior A) = interior A`.
      simpa [interior_interior] using interior_maximal h_cl isOpen_interior
    -- Conclude using the above inclusion.
    exact h_subset hx_intA