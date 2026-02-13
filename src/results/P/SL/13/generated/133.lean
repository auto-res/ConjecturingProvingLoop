

theorem Topology.interior_inter_subset_interior_intersection {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    (interior (A : Set X) ∩ interior B) ⊆ interior (A ∩ B) := by
  -- Let `x` be in the left-hand set.
  intro x hx
  -- The set `interior A ∩ interior B` is open.
  have h_open : IsOpen ((interior (A : Set X)) ∩ interior B) :=
    (isOpen_interior : IsOpen (interior (A : Set X))).inter isOpen_interior
  -- Moreover, it is contained in `A ∩ B`.
  have h_subset :
      ((interior (A : Set X)) ∩ interior B : Set X) ⊆ A ∩ B := by
    intro y hy
    exact ⟨(interior_subset : interior (A : Set X) ⊆ A) hy.1,
           (interior_subset : interior B ⊆ B) hy.2⟩
  -- Since `x` belongs to an open subset of `A ∩ B`, it lies in `interior (A ∩ B)`.
  have : x ∈ interior (A ∩ B) :=
    (interior_maximal (s := A ∩ B) h_subset h_open) hx
  exact this