

theorem P1_map_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {A : Set X} : Topology.P1 (e '' A) ↔ Topology.P1 A := by
  constructor
  · intro h_image
    -- First, transport `P1` back with the inverse homeomorphism.
    have h_preimage : Topology.P1 (e.symm '' (e '' A)) :=
      (P1_image_homeomorph (e := e.symm) (A := e '' A)) h_image
    -- Show that this set is just `A`.
    have h_eq : (e.symm '' (e '' A) : Set X) = A := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨y, hy, hxy⟩
        rcases hy with ⟨z, hzA, rfl⟩
        -- Now `hxy : e.symm (e z) = x`.
        have hzx : z = x := by
          simpa [hxy] using (e.symm_apply_apply z).symm
        simpa [hzx] using hzA
      · intro hxA
        refine ⟨e x, ?_, ?_⟩
        · exact ⟨x, hxA, rfl⟩
        · simpa using e.symm_apply_apply x
    simpa [h_eq] using h_preimage
  · intro hA
    exact P1_image_homeomorph (e := e) hA

theorem P2_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : Topology.P2 A) (hB : Topology.P2 B) (hC : Topology.P2 C) : Topology.P2 ((Set.prod A B).prod C) := by
  -- First, obtain `P2` for `A × B`.
  have hAB : Topology.P2 (Set.prod A B) :=
    P2_prod (X := X) (Y := Y) (A := A) (B := B) hA hB
  -- Then combine this with `C` to get `P2` for `(A × B) × C`.
  have hABC : Topology.P2 ((Set.prod A B).prod C) :=
    P2_prod (X := X × Y) (Y := Z) (A := Set.prod A B) (B := C) hAB hC
  simpa using hABC