

theorem P3_union_distrib {X : Type*} [TopologicalSpace X] {A B C : Set X} : P3 (A ∪ (B ∩ C)) ↔ P3 ((A ∪ B) ∩ (A ∪ C)) := by
  simpa [Set.union_inter_distrib_left]

theorem P1_prod_assoc {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} : P1 (Set.prod (Set.prod A B) C) ↔ P1 (Set.prod A (Set.prod B C)) := by
  -- Abbreviate the associativity homeomorphism.
  let e := Homeomorph.prodAssoc X Y Z
  ------------------------------------------------------------------
  -- 1.  Identify the image of `(A ×ˢ B) ×ˢ C` under `e`.
  ------------------------------------------------------------------
  have hImage :
      (e '' (Set.prod (Set.prod A B) C) :
          Set (X × (Y × Z))) = Set.prod A (Set.prod B C) := by
    ext x
    constructor
    · -- `x` comes from the image.
      rintro ⟨p, hp, rfl⟩
      rcases p with ⟨⟨a, b⟩, c⟩
      rcases hp with ⟨⟨ha, hb⟩, hc⟩
      exact ⟨ha, ⟨hb, hc⟩⟩
    · -- Conversely, start with `x ∈ A ×ˢ (B ×ˢ C)`.
      intro hx
      rcases x with ⟨a, bc⟩
      rcases bc with ⟨b, c⟩
      rcases hx with ⟨ha, ⟨hb, hc⟩⟩
      refine ⟨((a, b), c), ?_, ?_⟩
      · exact ⟨⟨ha, hb⟩, hc⟩
      · -- `e ((a, b), c) = (a, (b, c))` by definition.
        rfl
  ------------------------------------------------------------------
  -- 2.  Transport the `P1` property along the homeomorphism and
  --     rewrite using `hImage`.
  ------------------------------------------------------------------
  have hEquiv :
      P1 (Set.prod (Set.prod A B) C) ↔ P1 (Set.prod A (Set.prod B C)) := by
    -- `P1 (e '' S) ↔ P1 S`
    have h :=
      (P1_image_homeomorph_iff
          (e := e)
          (A := Set.prod (Set.prod A B) C))
    -- Rewrite the left‐hand side via `hImage` and reverse the equivalence.
    simpa [hImage] using h.symm
  ------------------------------------------------------------------
  -- 3.  Conclude.
  ------------------------------------------------------------------
  simpa using hEquiv

theorem P3_constant_map {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {c : Y} : P3 ({x : X | True}) := by
  simpa using (P3_univ (X := X))

theorem P1_sigma {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] {A : ∀ i, Set (X i)} : (∀ i, P1 (A i)) → P1 {x : Σ i, X i | x.2 ∈ A x.1} := by
  classical
  intro hP1
  -- `S` is the σ–type set we are interested in.
  intro x hx
  rcases x with ⟨i, a⟩
  -- Interpret the membership hypothesis in the fibre `i`.
  have ha : a ∈ A i := by
    simpa using hx
  -- Apply the `P1` property in the fibre.
  have h_cl_fibre : a ∈ closure (interior (A i)) := (hP1 i) ha
  ------------------------------------------------------------------
  -- Goal: `(i , a)` belongs to `closure (interior S)`.
  ------------------------------------------------------------------
  have h_closure :
      (⟨i, a⟩ : Σ j, X j) ∈
        closure (interior {y : Σ j, X j | y.2 ∈ A y.1}) := by
    -- Neighbourhood characterisation of the closure.
    apply (mem_closure_iff).2
    intro U hUopen hUa
    ----------------------------------------------------------------
    -- Slice the neighbourhood `U` in the fibre `i`.
    ----------------------------------------------------------------
    let V : Set (X i) := {y | (⟨i, y⟩ : Σ j, X j) ∈ U}
    have hVopen : IsOpen V := by
      have hSlice := (isOpen_sigma_iff).1 hUopen i
      simpa [V] using hSlice
    have haV : a ∈ V := by
      have : (⟨i, a⟩ : Σ j, X j) ∈ U := hUa
      simpa [V] using this
    ----------------------------------------------------------------
    -- Use the closure property in the fibre to get a point in
    -- `V ∩ interior (A i)`.
    ----------------------------------------------------------------
    have h_nonempty : ((V ∩ interior (A i)) : Set (X i)).Nonempty :=
      (mem_closure_iff).1 h_cl_fibre V hVopen haV
    rcases h_nonempty with ⟨b, hbV, hbIntAi⟩
    ----------------------------------------------------------------
    -- 1.  `(i , b)` lies in `U`.
    ----------------------------------------------------------------
    have hbU : (⟨i, b⟩ : Σ j, X j) ∈ U := by
      have : b ∈ V := hbV
      simpa [V] using this
    ----------------------------------------------------------------
    -- 2.  `(i , b)` lies in `interior S`.
    ----------------------------------------------------------------
    -- Define the auxiliary open set
    let S₂ : Set (Σ j, X j) := {y | y.2 ∈ interior (A y.1)}
    -- `S₂` is open:
    have hS₂_open : IsOpen S₂ := by
      -- Check the slices of `S₂`.
      have hSlices :
          ∀ j, IsOpen {y : X j | (⟨j, y⟩ : Σ k, X k) ∈ S₂} := by
        intro j
        have hEq :
            {y : X j | (⟨j, y⟩ : Σ k, X k) ∈ S₂} = interior (A j) := by
          ext y; simp [S₂]
        simpa [hEq] using isOpen_interior
      simpa [S₂] using (isOpen_sigma_iff).2 hSlices
    -- `S₂ ⊆ S`, hence `S₂ ⊆ interior S`.
    have hS₂_sub :
        (S₂ : Set (Σ j, X j)) ⊆
          {y : Σ j, X j | y.2 ∈ A y.1} := by
      intro y hy
      dsimp [S₂] at hy
      dsimp
      exact (interior_subset : interior (A y.1) ⊆ A y.1) hy
    have hS₂_to_int :
        (S₂ : Set (Σ j, X j)) ⊆
          interior {y : Σ j, X j | y.2 ∈ A y.1} :=
      interior_maximal hS₂_sub hS₂_open
    -- `(i , b)` belongs to `S₂`.
    have hbS₂ : (⟨i, b⟩ : Σ j, X j) ∈ S₂ := by
      dsimp [S₂]; simpa [hbIntAi]
    -- Hence `(i , b)` is in `interior S`.
    have hbIntS :
        (⟨i, b⟩ : Σ j, X j) ∈
          interior {y : Σ j, X j | y.2 ∈ A y.1} :=
      hS₂_to_int hbS₂
    -- Provide the required witness in `U ∩ interior S`.
    exact ⟨⟨i, b⟩, hbU, hbIntS⟩
  -- Conclude.
  simpa using h_closure