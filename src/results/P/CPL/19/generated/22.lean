

theorem P1_prod_swap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P1 (Set.prod A B) → P1 (Set.prod B A) := by
  intro hP1
  ----------------------------------------------------------------
  -- Step 1: transport the `P1` property along the swap homeomorphism.
  ----------------------------------------------------------------
  have hImage :
      P1 ((Homeomorph.prodComm X Y) '' (Set.prod A B)) :=
    P1_image_homeomorph
      (e := Homeomorph.prodComm X Y) (A := Set.prod A B) hP1
  ----------------------------------------------------------------
  -- Step 2: identify that image with `B ×ˢ A`.
  ----------------------------------------------------------------
  have hImage_eq :
      ((Homeomorph.prodComm X Y) '' (Set.prod A B) :
        Set (Y × X)) = Set.prod B A := by
    ext z
    constructor
    · -- `z` comes from the image
      rintro ⟨p, hpAB, rfl⟩
      rcases hpAB with ⟨hpA, hpB⟩
      exact ⟨hpB, hpA⟩
    · -- conversely, start with `z ∈ B ×ˢ A`
      intro hz
      rcases z with ⟨b, a⟩
      have hz' : (b, a) ∈ Set.prod B A := hz
      rcases hz' with ⟨hb, ha⟩
      refine ⟨(a, b), ?_, rfl⟩
      exact ⟨ha, hb⟩
  ----------------------------------------------------------------
  -- Step 3: rewrite and conclude.
  ----------------------------------------------------------------
  exact (hImage_eq ▸ hImage)

theorem P2_prod_swap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P2 (Set.prod A B) → P2 (Set.prod B A) := by
  intro hP2AB
  ----------------------------------------------------------------
  -- Step 1: transport the `P2` property along the swap homeomorphism.
  ----------------------------------------------------------------
  have hImage :
      P2 ((Homeomorph.prodComm X Y) '' (Set.prod A B)) :=
    P2_image_homeomorph
      (e := Homeomorph.prodComm X Y) (A := Set.prod A B) hP2AB
  -- The underlying map of `prodComm` is `Prod.swap`, so we rewrite.
  have hImage' : P2 (Prod.swap '' (Set.prod A B)) := by
    simpa using hImage
  ----------------------------------------------------------------
  -- Step 2: identify this image with `B ×ˢ A`.
  ----------------------------------------------------------------
  have hSwap_eq :
      (Prod.swap '' (Set.prod A B) : Set (Y × X)) = Set.prod B A := by
    ext z
    constructor
    · rintro ⟨p, hpAB, rfl⟩
      rcases hpAB with ⟨hpA, hpB⟩
      exact ⟨hpB, hpA⟩
    · intro hz
      rcases z with ⟨b, a⟩
      rcases hz with ⟨hb, ha⟩
      exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
  ----------------------------------------------------------------
  -- Step 3: rewrite and conclude.
  ----------------------------------------------------------------
  simpa [hSwap_eq] using hImage'

theorem P3_prod_swap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P3 (Set.prod A B) → P3 (Set.prod B A) := by
  intro hP3
  -- Step 1: transport `P3` along the swap homeomorphism.
  have hImage :
      P3 ((Homeomorph.prodComm X Y) '' (Set.prod A B)) :=
    P3_image_homeomorph
      (e := Homeomorph.prodComm X Y) (A := Set.prod A B) hP3
  -- Step 2: identify that image with `B ×ˢ A`.
  have hImage_eq :
      ((Homeomorph.prodComm X Y) '' (Set.prod A B) :
        Set (Y × X)) = Set.prod B A := by
    ext z
    constructor
    · rintro ⟨p, hpAB, rfl⟩
      rcases hpAB with ⟨hpA, hpB⟩
      exact ⟨hpB, hpA⟩
    · intro hz
      rcases z with ⟨b, a⟩
      have hz' : (b, a) ∈ Set.prod B A := hz
      rcases hz' with ⟨hb, ha⟩
      refine ⟨(a, b), ?_, rfl⟩
      exact ⟨ha, hb⟩
  -- Step 3: rewrite and conclude.
  exact (hImage_eq ▸ hImage)