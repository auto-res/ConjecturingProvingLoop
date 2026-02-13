

theorem P3_prod_comm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : (Topology.P3 (A.prod B)) ↔ Topology.P3 (B.prod A) := by
  constructor
  · intro h
    -- transport `P3` through the coordinate‐swap homeomorphism
    have h_image :
        Topology.P3
          ((fun p : X × Y => Prod.swap p) '' (A.prod B) : Set (Y × X)) := by
      simpa using
        (P3_image_homeomorph
            (e := Homeomorph.prodComm (X := X) (Y := Y))
            (A := A.prod B)) h
    -- identify this image with `B × A`
    have h_eq :
        ((fun p : X × Y => Prod.swap p) '' (A.prod B) : Set (Y × X)) =
          B.prod A := by
      ext p
      constructor
      · rintro ⟨⟨x, y⟩, hxy, rfl⟩
        rcases hxy with ⟨hxA, hyB⟩
        exact And.intro hyB hxA
      · intro hp
        rcases p with ⟨y, x⟩
        rcases hp with ⟨hyB, hxA⟩
        refine ⟨(x, y), ?_, rfl⟩
        exact And.intro hxA hyB
    simpa [h_eq] using h_image
  · intro h
    -- transport in the opposite direction
    have h_image :
        Topology.P3
          ((fun p : Y × X => Prod.swap p) '' (B.prod A) : Set (X × Y)) := by
      simpa using
        (P3_image_homeomorph
            (e := Homeomorph.prodComm (X := Y) (Y := X))
            (A := B.prod A)) h
    -- identify this image with `A × B`
    have h_eq :
        ((fun p : Y × X => Prod.swap p) '' (B.prod A) : Set (X × Y)) =
          A.prod B := by
      ext p
      constructor
      · rintro ⟨⟨y, x⟩, hxy, rfl⟩
        rcases hxy with ⟨hyB, hxA⟩
        exact And.intro hxA hyB
      · intro hp
        rcases p with ⟨x, y⟩
        rcases hp with ⟨hxA, hyB⟩
        refine ⟨(y, x), ?_, rfl⟩
        exact And.intro hyB hxA
    simpa [h_eq] using h_image

theorem P3_preimage_open_map {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) (h_open : IsOpenMap f) {B : Set Y} (hB : Topology.P3 B) : Topology.P3 (f ⁻¹' B) := by
  -- Unpack the assumption `P3 B`.
  dsimp [Topology.P3] at hB
  -- Unfold the goal.
  dsimp [Topology.P3]
  intro x hx
  -- From `hx` we know `f x ∈ B`.
  have hfxB : f x ∈ (B : Set Y) := hx
  -- Hence `f x` belongs to the interior of `closure B`.
  have hfx_int : f x ∈ interior (closure (B : Set Y)) := hB hfxB
  -- Define the open set `S = f ⁻¹' interior (closure B)`.
  have hS_open :
      IsOpen (f ⁻¹' interior (closure (B : Set Y))) :=
    (isOpen_interior.preimage hf)
  have hxS : x ∈ f ⁻¹' interior (closure (B : Set Y)) := hfx_int
  -- We show that `S ⊆ closure (f ⁻¹' B)`.
  have hS_sub :
      (f ⁻¹' interior (closure (B : Set Y))) ⊆
        closure (f ⁻¹' (B : Set Y)) := by
    intro z hz
    -- First, note that `f z ∈ closure B`.
    have h_clB : f z ∈ closure (B : Set Y) := by
      have : interior (closure (B : Set Y)) ⊆ closure B := interior_subset
      exact this hz
    -- Prove that `z` is in the closure of `f ⁻¹' B`.
    have hz_cl : z ∈ closure (f ⁻¹' (B : Set Y)) := by
      -- Use the neighbourhood characterization of the closure.
      apply (mem_closure_iff).2
      intro V hVopen hzV
      -- The image `f '' V` is open and contains `f z`.
      have h_fV_open : IsOpen (f '' V) := h_open _ hVopen
      have hfzV : f z ∈ f '' V := ⟨z, hzV, rfl⟩
      -- Hence it meets `B`.
      have h_nonempty :
          ((f '' V) ∩ (B : Set Y)).Nonempty :=
        (mem_closure_iff).1 h_clB _ h_fV_open hfzV
      rcases h_nonempty with ⟨y, ⟨⟨w, hwV, rfl⟩, hyB⟩⟩
      -- `w` is in `V ∩ f ⁻¹' B`.
      exact ⟨w, by
        refine ⟨hwV, ?_⟩
        simpa using hyB⟩
    exact hz_cl
  -- By maximality of the interior, we obtain the desired inclusion.
  have hS_sub_int :
      (f ⁻¹' interior (closure (B : Set Y))) ⊆
        interior (closure (f ⁻¹' (B : Set Y))) :=
    interior_maximal hS_sub hS_open
  -- Conclude for the original point `x`.
  exact hS_sub_int hxS