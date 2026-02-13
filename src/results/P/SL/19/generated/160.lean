

theorem Topology.interior_inter_subset_and_isOpen_of_open {X : Type*}
    [TopologicalSpace X] {A B : Set X} (hB : IsOpen B) :
    ((interior A ∩ B : Set X) ⊆ A ∩ B) ∧ IsOpen (interior A ∩ B) := by
  constructor
  · intro x hx
    exact And.intro (interior_subset hx.1) hx.2
  · exact isOpen_interior.inter hB