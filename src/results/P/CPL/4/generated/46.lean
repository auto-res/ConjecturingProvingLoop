

theorem P1_iInter_decreasing {ι : Sort _} {X : Type*} [TopologicalSpace X] {s : ι → Set X} (hdec : ∀ i j, s j ⊆ s i) (h : ∀ i, Topology.P1 (s i)) : Topology.P1 (⋂ i, s i) := by
  classical
  by_cases hne : (Nonempty ι)
  · -- The index type is inhabited: pick an index `i₀`.
    rcases hne with ⟨i₀⟩
    -- First, identify the intersection with `s i₀`.
    have h_eq : (⋂ i, s i : Set X) = s i₀ := by
      apply Set.Subset.antisymm
      · intro x hx
        exact (Set.mem_iInter.1 hx) i₀
      · intro x hx
        have hx_all : ∀ j, x ∈ s j := by
          intro j
          have h_subset : (s i₀ : Set X) ⊆ s j := hdec j i₀
          exact h_subset hx
        exact (Set.mem_iInter.2 hx_all)
    -- Apply `P1` to `s i₀` and rewrite using the equality above.
    have hP1_i0 : Topology.P1 (s i₀) := h i₀
    simpa [h_eq] using hP1_i0
  · -- The index type is empty: the intersection is `univ`.
    haveI : IsEmpty ι := ⟨fun i => (hne ⟨i⟩).elim⟩
    have h_eq_univ : (⋂ i, s i : Set X) = (Set.univ : Set X) := by
      ext x
      simp [Set.mem_iInter]
    simpa [h_eq_univ] using (P1_univ (X := X))

theorem P2_iInter_decreasing {ι : Sort _} {X : Type*} [TopologicalSpace X] {s : ι → Set X} (hdec : ∀ i j, s j ⊆ s i) (h : ∀ i, Topology.P2 (s i)) : Topology.P2 (⋂ i, s i) := by
  -- First, obtain `P1` for the intersection using the decreasing property.
  have hP1 : Topology.P1 (⋂ i, s i) :=
    P1_iInter_decreasing (s := s) hdec
      (fun i => P2_implies_P1 (A := s i) (h i))
  -- Next, obtain `P3` for the intersection in the same way.
  have hP3 : Topology.P3 (⋂ i, s i) :=
    P3_iInter_decreasing (s := s) hdec
      (fun i => P2_implies_P3 (A := s i) (h i))
  -- Combine the two properties to get `P2`.
  simpa using
    (P2_iff_P1_and_P3 (A := ⋂ i, s i)).2 ⟨hP1, hP3⟩

theorem P1_prod_symmetric {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : Topology.P1 (Set.prod A B) ↔ Topology.P1 (Set.prod B A) := by
  -- Define the swapping homeomorphism
  let e := Homeomorph.prodComm X Y
  -- Characterise its action on the rectangle `A × B`.
  have h_img :
      (e '' (Set.prod A B) : Set (Y × X)) = Set.prod B A := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases hq with ⟨hA, hB⟩
      exact And.intro hB hA
    · rintro hp
      rcases p with ⟨b, a⟩
      rcases hp with ⟨hB, hA⟩
      refine ⟨(a, b), ?_, ?_⟩
      · exact And.intro hA hB
      · rfl
  -- And similarly for the inverse map.
  have h_img_symm :
      (e.symm '' (Set.prod B A) : Set (X × Y)) = Set.prod A B := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases hq with ⟨hB, hA⟩
      exact And.intro hA hB
    · rintro hp
      rcases p with ⟨a, b⟩
      rcases hp with ⟨hA, hB⟩
      refine ⟨(b, a), ?_, ?_⟩
      · exact And.intro hB hA
      · rfl
  -- Transfer the property through the homeomorphism and its inverse.
  constructor
  · intro hP1
    have h := P1_image_homeomorph (e := e) (A := Set.prod A B) hP1
    simpa [h_img] using h
  · intro hP1
    have h := P1_image_homeomorph (e := e.symm) (A := Set.prod B A) hP1
    simpa [h_img_symm] using h

theorem P3_prod_symmetric {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : Topology.P3 (Set.prod A B) ↔ Topology.P3 (Set.prod B A) := by
  -- Swapping homeomorphism
  let e := Homeomorph.prodComm X Y
  -- Image of `A × B` under `e`
  have h_img :
      (e '' Set.prod A B : Set (Y × X)) = Set.prod B A := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases hq with ⟨hA, hB⟩
      exact And.intro hB hA
    · rintro hp
      rcases p with ⟨b, a⟩
      rcases hp with ⟨hB, hA⟩
      refine ⟨(a, b), ?_, ?_⟩
      · exact And.intro hA hB
      · rfl
  -- Image of `B × A` under `e.symm`
  have h_img_symm :
      (e.symm '' Set.prod B A : Set (X × Y)) = Set.prod A B := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases hq with ⟨hB, hA⟩
      exact And.intro hA hB
    · rintro hp
      rcases p with ⟨a, b⟩
      rcases hp with ⟨hA, hB⟩
      refine ⟨(b, a), ?_, ?_⟩
      · exact And.intro hB hA
      · rfl
  -- Transfer the `P3` property through the homeomorphism.
  constructor
  · intro hP3
    have h :=
      P3_image_homeomorph
        (e := e) (A := Set.prod A B) hP3
    simpa [h_img] using h
  · intro hP3
    have h :=
      P3_image_homeomorph
        (e := e.symm) (A := Set.prod B A) hP3
    simpa [h_img_symm] using h

theorem P2_subsingleton_space {X : Type*} [TopologicalSpace X] [Subsingleton X] (A : Set X) : Topology.P2 A := by
  classical
  by_cases hA : (A : Set X) = ∅
  · -- Empty set case
    simpa [hA] using (P2_empty (X := X))
  · -- Non-empty case: in a subsingleton space this forces `A = univ`
    have hAuniv : (A : Set X) = (Set.univ : Set X) := by
      -- Pick an element of `A`
      obtain ⟨a, ha⟩ := (Set.nonempty_iff_ne_empty).2 hA
      -- Show that every element belongs to `A`
      ext x
      constructor
      · intro _; trivial
      · intro _
        have : x = a := Subsingleton.elim _ _
        simpa [this] using ha
    -- Conclude using the fact that `univ` satisfies `P2`
    simpa [hAuniv] using (P2_univ (X := X))

theorem P3_subsingleton_space {X : Type*} [TopologicalSpace X] [Subsingleton X] (A : Set X) : Topology.P3 A := by
  classical
  by_cases hA : (A : Set X) = ∅
  · simpa [hA] using (P3_empty (X := X))
  ·
    -- In a non‐empty set of a subsingleton space we actually have `A = univ`.
    have hAuniv : (A : Set X) = (Set.univ : Set X) := by
      -- Pick an element of `A`.
      obtain ⟨a, ha⟩ := (Set.nonempty_iff_ne_empty).2 hA
      ext x
      constructor
      · intro _; trivial
      · intro _
        -- All points are equal in a subsingleton space.
        have : x = a := Subsingleton.elim _ _
        simpa [this] using ha
    -- Conclude using the fact that `univ` satisfies `P3`.
    simpa [hAuniv] using (P3_univ (X := X))