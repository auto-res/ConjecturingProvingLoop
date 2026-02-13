

theorem P1_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (e : X ≃ₜ Y) (hA : P1 A) : P1 (e '' A) := by
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x` lies in `A`, hence in `closure (interior A)`.
  have hx_cl : x ∈ closure (interior A) := hA hxA
  -- Apply `e` to obtain a membership in the image of that closure.
  have h1 : e x ∈ (⇑e) '' closure (interior A) := ⟨x, hx_cl, rfl⟩
  -- Relate this image to the closure of the image of `interior A`.
  have h_image_closure :
      (⇑e) '' closure (interior A) =
        closure ((⇑e) '' interior A) := by
    simpa using e.image_closure (s := interior A)
  -- Relate the image of `interior A` to the interior of the image of `A`.
  have h_image_interior :
      (⇑e) '' interior A =
        interior ((⇑e) '' A) := by
    simpa using e.image_interior (s := A)
  -- Assemble the pieces.
  have : e x ∈ closure (interior ((⇑e) '' A)) := by
    have : e x ∈ closure ((⇑e) '' interior A) := by
      simpa [h_image_closure] using h1
    simpa [h_image_interior] using this
  simpa using this

theorem P2_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : P2 A := by
  classical
  by_cases hA_empty : (A : Set X) = ∅
  · simpa [hA_empty] using (P2_empty (X := X))
  ·
    have h_nonempty : (A : Set X).Nonempty :=
      (Set.nonempty_iff_ne_empty).mpr hA_empty
    rcases h_nonempty with ⟨x0, hx0A⟩
    have hA_univ : (A : Set X) = Set.univ := by
      ext y
      constructor
      · intro _; simp
      · intro _
        have h_eq : y = x0 := Subsingleton.elim _ _
        simpa [h_eq] using hx0A
    simpa [hA_univ] using (P2_univ (X := X))