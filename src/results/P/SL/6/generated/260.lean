

theorem closure_interior_iUnion_eq_closure_iUnion_of_open
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {S : ι → Set X}
    (hS : ∀ i, IsOpen (S i)) :
    closure (interior ((⋃ i, S i) : Set X)) = closure (⋃ i, S i) := by
  -- The union of open sets is open.
  have hOpen : IsOpen ((⋃ i, S i) : Set X) := by
    simpa using isOpen_iUnion (fun i => hS i)
  -- For an open set, its interior equals itself.
  have hInt : interior ((⋃ i, S i) : Set X) = ⋃ i, S i := hOpen.interior_eq
  simpa [hInt]