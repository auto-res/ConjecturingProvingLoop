

theorem P1_of_closure_subset {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure A ⊆ closure (interior A)) : P1 A := by
  intro x hxA
  exact h (subset_closure hxA)

theorem P1_prod_comm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P1 (Set.prod A B) ↔ P1 (Set.prod B A) := by
  constructor
  · -- `P1 (A ×ˢ B) → P1 (B ×ˢ A)`
    intro hP1
    intro p hpBA
    -- Homeomorphism that swaps the coordinates.
    let e : (Y × X) ≃ₜ (X × Y) := (Homeomorph.prodComm X Y).symm
    have e_apply : (⇑e) = Prod.swap := rfl
    ----------------------------------------------------------------
    -- 1.  Transport `p` to `A ×ˢ B` and apply `hP1`.
    ----------------------------------------------------------------
    have hpAB : (⇑e) p ∈ Set.prod A B := by
      rcases hpBA with ⟨hpB, hpA⟩
      simpa [Set.prod, e_apply] using And.intro hpA hpB
    have h_cl_AB : (⇑e) p ∈ closure (interior (Set.prod A B)) :=
      hP1 hpAB
    ----------------------------------------------------------------
    -- 2.  Relate the two closures through `e`.
    ----------------------------------------------------------------
    -- `e '' (B ×ˢ A) = A ×ˢ B`
    have h_swap_prod : (⇑e) '' (Set.prod B A) = Set.prod A B := by
      ext q
      constructor
      · rintro ⟨r, hrBA, rfl⟩
        rcases hrBA with ⟨hrB, hrA⟩
        simpa [Set.prod, e_apply] using And.intro hrA hrB
      · intro hqAB
        rcases q with ⟨a, b⟩
        dsimp [Set.prod] at hqAB
        rcases hqAB with ⟨haA, hbB⟩
        have h_pre : (b, a) ∈ Set.prod B A := by
          exact And.intro hbB haA
        refine ⟨(b, a), h_pre, ?_⟩
        simp [e_apply]
    -- `e '' interior (B ×ˢ A) = interior (A ×ˢ B)`
    have h_image_int :
        (⇑e) '' interior (Set.prod B A) = interior (Set.prod A B) := by
      have h := e.image_interior (s := Set.prod B A)
      simpa [h_swap_prod] using h
    -- `e '' closure (interior (B ×ˢ A)) = closure (interior (A ×ˢ B))`
    have h_image_cl :
        (⇑e) '' closure (interior (Set.prod B A)) =
          closure (interior (Set.prod A B)) := by
      have h := e.image_closure (s := interior (Set.prod B A))
      simpa [h_image_int] using h
    -- Use the equality to pull the membership back to `p`.
    have h_in_image :
        (⇑e) p ∈ (⇑e) '' closure (interior (Set.prod B A)) := by
      simpa [h_image_cl] using h_cl_AB
    rcases h_in_image with ⟨q, hq_cl, h_eq⟩
    have hq_eq : q = p := e.injective h_eq
    simpa [hq_eq] using hq_cl
  · -- `P1 (B ×ˢ A) → P1 (A ×ˢ B)`  (same argument with roles swapped)
    intro hP1
    intro p hpAB
    -- Homeomorphism that swaps the coordinates (opposite direction).
    let e : (X × Y) ≃ₜ (Y × X) := Homeomorph.prodComm X Y
    have e_apply : (⇑e) = Prod.swap := rfl
    ----------------------------------------------------------------
    -- 1.  Transport `p` to `B ×ˢ A` and apply `hP1`.
    ----------------------------------------------------------------
    have hpBA : (⇑e) p ∈ Set.prod B A := by
      rcases hpAB with ⟨hpA, hpB⟩
      simpa [Set.prod, e_apply] using And.intro hpB hpA
    have h_cl_BA : (⇑e) p ∈ closure (interior (Set.prod B A)) :=
      hP1 hpBA
    ----------------------------------------------------------------
    -- 2.  Relate the closures through `e`.
    ----------------------------------------------------------------
    -- `e '' (A ×ˢ B) = B ×ˢ A`
    have h_swap_prod : (⇑e) '' (Set.prod A B) = Set.prod B A := by
      ext q
      constructor
      · rintro ⟨r, hrAB, rfl⟩
        rcases hrAB with ⟨hrA, hrB⟩
        simpa [Set.prod, e_apply] using And.intro hrB hrA
      · intro hqBA
        rcases q with ⟨b, a⟩
        dsimp [Set.prod] at hqBA
        rcases hqBA with ⟨hbB, haA⟩
        have h_pre : (a, b) ∈ Set.prod A B := by
          exact And.intro haA hbB
        refine ⟨(a, b), h_pre, ?_⟩
        simp [e_apply]
    -- `e '' interior (A ×ˢ B) = interior (B ×ˢ A)`
    have h_image_int :
        (⇑e) '' interior (Set.prod A B) = interior (Set.prod B A) := by
      have h := e.image_interior (s := Set.prod A B)
      simpa [h_swap_prod] using h
    -- `e '' closure (interior (A ×ˢ B)) = closure (interior (B ×ˢ A))`
    have h_image_cl :
        (⇑e) '' closure (interior (Set.prod A B)) =
          closure (interior (Set.prod B A)) := by
      have h := e.image_closure (s := interior (Set.prod A B))
      simpa [h_image_int] using h
    -- Pull membership back.
    have h_in_image :
        (⇑e) p ∈ (⇑e) '' closure (interior (Set.prod A B)) := by
      simpa [h_image_cl] using h_cl_BA
    rcases h_in_image with ⟨q, hq_cl, h_eq⟩
    have hq_eq : q = p := e.injective h_eq
    simpa [hq_eq] using hq_cl

theorem P1_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : P1 A := by
  classical
  by_cases hA_empty : (A : Set X) = ∅
  · -- If `A` is empty, we use the lemma `P1_empty`.
    simpa [hA_empty] using (P1_empty (X := X))
  · -- Otherwise, `A` is non-empty.
    -- Obtain an element `x0 ∈ A`.
    have h_nonempty : (A : Set X).Nonempty := by
      have : (A : Set X) ≠ ∅ := hA_empty
      exact (Set.nonempty_iff_ne_empty).mpr this
    rcases h_nonempty with ⟨x0, hx0A⟩
    -- In a subsingleton type every element equals `x0`, hence `A = univ`.
    have hA_univ : (A : Set X) = Set.univ := by
      ext y
      constructor
      · intro _; simp
      · intro _
        have h_eq : y = x0 := Subsingleton.elim _ _
        simpa [h_eq] using hx0A
    -- Conclude using `P1_univ`.
    simpa [hA_univ] using (P1_univ (X := X))