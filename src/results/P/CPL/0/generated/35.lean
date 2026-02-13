

theorem P3_product {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P3 A → P3 B → P3 (Set.prod A B) := by
  intro hP3A hP3B
  intro p hp
  -- Split the point `p` into its coordinates.
  rcases p with ⟨x, y⟩
  change (x, y) ∈ Set.prod A B at hp
  have hxA : x ∈ A := hp.1
  have hyB : y ∈ B := hp.2
  -- Apply the `P3` hypotheses on the two coordinates.
  have hx_int : x ∈ interior (closure (A : Set X)) := hP3A hxA
  have hy_int : y ∈ interior (closure (B : Set Y)) := hP3B hyB
  ----------------------------------------------------------------------
  -- An open neighbourhood of `(x, y)` lying inside the desired interior.
  ----------------------------------------------------------------------
  let S : Set (X × Y) :=
    Set.prod (interior (closure (A : Set X))) (interior (closure (B : Set Y)))
  have h_mem_S : (x, y) ∈ (S : Set (X × Y)) := by
    dsimp [S]; exact And.intro hx_int hy_int
  have hS_open : IsOpen (S : Set (X × Y)) := by
    dsimp [S]; exact isOpen_interior.prod isOpen_interior
  ----------------------------------------------------------------------
  -- Show that `S` is contained in `closure (A ×ˢ B)`.
  ----------------------------------------------------------------------
  have hS_sub_closure : (S : Set (X × Y)) ⊆ closure (Set.prod A B) := by
    intro q hq
    rcases hq with ⟨hq1, hq2⟩
    -- Each coordinate lies in the respective closure.
    have hq1_cl : q.1 ∈ closure (A : Set X) :=
      (interior_subset : interior (closure (A : Set X)) ⊆ closure (A : Set X)) hq1
    have hq2_cl : q.2 ∈ closure (B : Set Y) :=
      (interior_subset : interior (closure (B : Set Y)) ⊆ closure (B : Set Y)) hq2
    have hq_prod : (q : X × Y) ∈
        Set.prod (closure (A : Set X)) (closure (B : Set Y)) :=
      And.intro hq1_cl hq2_cl
    -- Identify this product with the required closure via `closure_prod_eq`.
    have h_eq :
        closure (Set.prod A B) =
          Set.prod (closure (A : Set X)) (closure (B : Set Y)) := by
      simpa using
        (closure_prod_eq :
          closure (Set.prod A B) =
            closure (A : Set X) ×ˢ closure (B : Set Y))
    simpa [h_eq] using hq_prod
  ----------------------------------------------------------------------
  -- Since `S` is open, it is contained in the interior of that closure.
  ----------------------------------------------------------------------
  have hS_sub_int :
      (S : Set (X × Y)) ⊆ interior (closure (Set.prod A B)) :=
    interior_maximal hS_sub_closure hS_open
  ----------------------------------------------------------------------
  -- Conclude.
  ----------------------------------------------------------------------
  exact hS_sub_int h_mem_S

theorem P2_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ Y) {A : Set X} : P2 A → P2 (f '' A) := by
  intro hP2
  -- Obtain `P1` and `P3` for `A` from `P2 A`.
  have hP1A : P1 A := P2_imp_P1 hP2
  have hP3A : P3 A := P2_imp_P3 hP2
  -- Transport these properties through the homeomorphism.
  have hP1_image : P1 (f '' A) := P1_image_homeomorph f hP1A
  have hP3_image : P3 (f '' A) := P3_image_homeomorph f hP3A
  -- Combine them to get `P2` for `f '' A`.
  exact (P2_iff_P1_and_P3).2 ⟨hP1_image, hP3_image⟩