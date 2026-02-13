

theorem P1_iUnion_interior {X I} [TopologicalSpace X] {F : I → Set X} (h : ∀ i, P1 (F i)) : P1 (⋃ i, interior (F i)) := by
  intro x hx
  -- The union of interiors is open, hence its interior is itself.
  have h_open : IsOpen (⋃ i, interior (F i)) := by
    apply isOpen_iUnion
    intro i
    exact isOpen_interior
  have h_int_eq : interior (⋃ i, interior (F i)) = ⋃ i, interior (F i) :=
    h_open.interior_eq
  -- From `x ∈ ⋃ i, interior (F i)` we get `x ∈ closure (⋃ i, interior (F i))`.
  have hx_cl : x ∈ closure (⋃ i, interior (F i)) := subset_closure hx
  -- Rewrite the target using `h_int_eq`.
  simpa [h_int_eq] using hx_cl