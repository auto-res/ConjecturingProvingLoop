

theorem P3_inter_open {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : IsOpen A) (hB : IsOpen B) : Topology.P3 (A ∩ B) := by
  have hOpen : IsOpen (A ∩ B) := hA.inter hB
  simpa using (Topology.P3_of_open (X := X) (A := A ∩ B) hOpen)

theorem P2_image_equiv {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (A : Set X) : Topology.P2 (e '' A) ↔ Topology.P2 A := by
  constructor
  · intro hImage
    -- Pull `P2` back through the inverse homeomorphism.
    have hPreimage : Topology.P2 (e.symm '' (e '' A)) :=
      P2_preimage_homeomorph (e := e) (B := e '' A) hImage
    -- Identify the pulled‐back set with `A`.
    have h_eq : (e.symm '' (e '' A) : Set X) = A := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨y, hy, hxy⟩
        rcases hy with ⟨z, hzA, rfl⟩
        have : z = x := by
          simpa [e.symm_apply_apply] using hxy
        simpa [this] using hzA
      · intro hxA
        refine ⟨e x, ?_, ?_⟩
        · exact ⟨x, hxA, rfl⟩
        · simpa using e.symm_apply_apply x
    simpa [h_eq] using hPreimage
  · intro hA
    exact P2_image_homeomorph (e := e) hA

theorem P3_prod_univ_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} (hA : Topology.P3 A) : Topology.P3 ((A.prod (Set.univ : Set Y)).prod (Set.univ : Set Z)) := by
  -- Obtain `P3` for `A × univ` on the second factor.
  have hAU : Topology.P3 (A.prod (Set.univ : Set Y)) :=
    (P3_prod_univ (X := X) (Y := Y) (A := A)) hA
  -- `univ` in `Z` satisfies `P3`.
  have hUnivZ : Topology.P3 (Set.univ : Set Z) := P3_univ (X := Z)
  -- Combine the two using the product lemma.
  simpa using
    (P3_prod
      (X := X × Y) (Y := Z)
      (A := (A.prod (Set.univ : Set Y)))
      (B := (Set.univ : Set Z))
      hAU hUnivZ)