

theorem P2_iff_isOpen_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed (A : Set X)) :
    Topology.P2 A ↔ IsOpen (A : Set X) := by
  dsimp [Topology.P2]
  constructor
  · intro hP2
    -- First, `closure (interior A)` is contained in `A` since `A` is closed.
    have hcl : closure (interior (A : Set X)) ⊆ (A : Set X) := by
      have : closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
        closure_mono (interior_subset : interior (A : Set X) ⊆ A)
      simpa [hA.closure_eq] using this
    -- Hence the target of `hP2` is contained in `interior A`.
    have hsubset : (A : Set X) ⊆ interior (A : Set X) := by
      have hmono : interior (closure (interior (A : Set X))) ⊆ interior (A : Set X) :=
        interior_mono hcl
      exact hP2.trans hmono
    -- `A` equals its interior, so it is open.
    have h_eq : interior (A : Set X) = A := by
      apply subset_antisymm
      · exact interior_subset
      · exact hsubset
    simpa [h_eq] using (isOpen_interior : IsOpen (interior (A : Set X)))
  · intro hOpen
    exact (Topology.isOpen_has_all_Ps (X := X) (A := A) hOpen).2.1