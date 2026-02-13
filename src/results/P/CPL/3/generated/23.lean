

theorem P1_inter_closure_subset {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (interior (closure A)) := by
  intro x hx
  simpa [interior_interior] using (subset_closure hx)

theorem P1_dense_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → closure (interior A) = closure A := by
  intro hP2
  exact (P1_iff_eq).1 (P2_subset_P1 hP2)

theorem P2_prod_swap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P2 (Set.prod A B) → P2 (Set.prod B A) := by
  intro hP2
  -- `p : Y × X`, `hp : p ∈ B ×ˢ A`
  intro p hp
  ----------------------------------------------------------------
  -- 0.  A few abbreviations.
  ----------------------------------------------------------------
  set sAB : Set (X × Y) := Set.prod A B
  set sBA : Set (Y × X) := Set.prod B A
  set S₁ : Set (Y × X) := interior (closure (interior sBA))
  set S₂ : Set (X × Y) := interior (closure (interior sAB))
  -- The coordinate–swap homeomorphism   (domain `Y × X`, codomain `X × Y`).
  let e : (Y × X) ≃ₜ (X × Y) := (Homeomorph.prodComm X Y).symm
  have e_apply : (⇑e) = Prod.swap := rfl
  ----------------------------------------------------------------
  -- 1.  Apply the hypothesis `hP2` to the swapped point.
  ----------------------------------------------------------------
  have h_mem_AB : (⇑e) p ∈ sAB := by
    rcases hp with ⟨hpB, hpA⟩
    simpa [sAB, sBA, e_apply] using And.intro hpA hpB
  have h_in_AB :
      (⇑e) p ∈ interior (closure (interior sAB)) :=
    hP2 h_mem_AB
  ----------------------------------------------------------------
  -- 2.  Show that `e '' S₁ = S₂`.
  ----------------------------------------------------------------
  have h_swap_prod : (⇑e) '' sBA = sAB := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases hq with ⟨hqB, hqA⟩
      simpa [sAB, sBA, e_apply] using And.intro hqA hqB
    · intro hx
      rcases x with ⟨a, b⟩
      dsimp [sAB] at hx
      rcases hx with ⟨haA, hbB⟩
      have hq : (b, a) ∈ sBA := by
        dsimp [sBA]; exact And.intro hbB haA
      refine ⟨(b, a), hq, ?_⟩
      simp [e_apply]
  have h_image :
      (⇑e) '' S₁ = S₂ := by
    -- unfold the two sets
    dsimp [S₁, S₂]
    -- first `image_interior`
    have h1 :
        (⇑e) '' interior (closure (interior sBA)) =
          interior ((⇑e) '' closure (interior sBA)) :=
      (e.image_interior (s := closure (interior sBA)))
    -- then `image_closure`
    have h2 :
        (⇑e) '' closure (interior sBA) =
          closure ((⇑e) '' interior sBA) :=
      (e.image_closure (s := interior sBA))
    -- next `image_interior` again
    have h3 :
        (⇑e) '' interior sBA =
          interior ((⇑e) '' sBA) :=
      (e.image_interior (s := sBA))
    -- combine everything
    simpa [h2, h3, h_swap_prod] using h1
  ----------------------------------------------------------------
  -- 3.  Transport the membership back to `p`.
  ----------------------------------------------------------------
  have h_in_image :
      (⇑e) p ∈ (⇑e) '' S₁ := by
    simpa [h_image] using h_in_AB
  rcases h_in_image with ⟨q, hqS₁, h_eq⟩
  -- `e` is injective, hence `q = p`.
  have h_qp : q = p := (e.injective h_eq)
  -- Finish.
  have hpS₁ : p ∈ S₁ := by
    simpa [h_qp] using hqS₁
  simpa [S₁] using hpS₁