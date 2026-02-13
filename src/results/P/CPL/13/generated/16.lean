

theorem P1_diff {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P1 A) (hB : IsClosed B) : Topology.P1 (A \ B) := by
  dsimp [Topology.P1] at *
  intro x hx
  have hxA : x ∈ A := hx.1
  have hx_notB : x ∉ B := hx.2
  have hx_cl : x ∈ closure (interior A) := hA hxA
  -- show `x ∈ closure (interior (A \ B))`
  have : x ∈ closure (interior (A \ B)) := by
    -- use the neighbourhood formulation of being in the closure
    apply (mem_closure_iff).2
    intro V hV hxV
    -- intersect the neighbourhood with `Bᶜ`
    have hB_open : IsOpen (Bᶜ : Set X) := by
      simpa using hB.isOpen_compl
    have hW_open : IsOpen (V ∩ Bᶜ) := IsOpen.inter hV hB_open
    have hxW : x ∈ V ∩ Bᶜ := And.intro hxV hx_notB
    -- by closeness of `interior A`, this set meets it
    have h_nonempty : ((V ∩ Bᶜ) ∩ interior A).Nonempty := by
      have h_mem := (mem_closure_iff).1 hx_cl
      have h := h_mem (V ∩ Bᶜ) hW_open hxW
      simpa [Set.inter_assoc, Set.inter_comm, Set.inter_left_comm] using h
    rcases h_nonempty with ⟨y, ⟨⟨hyV, hy_notB⟩, hy_intA⟩⟩
    -- build an open subset of `A \ B` containing `y`
    have hy_int_diff : y ∈ interior (A \ B) := by
      have hS_open : IsOpen (interior A ∩ Bᶜ : Set X) :=
        isOpen_interior.inter hB.isOpen_compl
      have hS_sub : (interior A ∩ Bᶜ : Set X) ⊆ A \ B := by
        intro z hz
        rcases hz with ⟨hz_intA, hz_notB⟩
        have hzA : z ∈ A := interior_subset hz_intA
        exact And.intro hzA hz_notB
      have hS_subset_int : (interior A ∩ Bᶜ : Set X) ⊆ interior (A \ B) :=
        interior_maximal hS_sub hS_open
      have hzS : y ∈ (interior A ∩ Bᶜ) := And.intro hy_intA hy_notB
      exact hS_subset_int hzS
    exact ⟨y, And.intro hyV hy_int_diff⟩
  exact this

theorem P2_prod_symm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : (Topology.P2 (Set.prod A B) ↔ Topology.P2 (Set.prod B A)) := by
  -- Let `e` be the homeomorphism swapping the two factors
  let e := (Homeomorph.prodComm X Y)
  -- The image of `A ×ˢ B` by `e` is `B ×ˢ A`
  have h_image_eq :
      (e '' (Set.prod A B) : Set (Y × X)) = Set.prod B A := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases q with ⟨x, y⟩
      dsimp [Set.prod] at hq ⊢
      rcases hq with ⟨hxA, hyB⟩
      simpa [e] using And.intro hyB hxA
    · intro hp
      rcases p with ⟨y, x⟩
      dsimp [Set.prod] at hp
      rcases hp with ⟨hyB, hxA⟩
      refine ⟨(x, y), ?_, ?_⟩
      · dsimp [Set.prod]
        exact And.intro hxA hyB
      · simpa [e]
  -- The preimage of `B ×ˢ A` by `e` is `A ×ˢ B`
  have h_preimage_eq :
      (e ⁻¹' (Set.prod B A) : Set (X × Y)) = Set.prod A B := by
    ext p
    constructor
    · intro hp
      dsimp [Set.preimage] at hp
      dsimp [e] at hp
      dsimp [Set.prod] at hp ⊢
      simpa [And.comm] using hp
    · intro hp
      dsimp [Set.preimage]
      dsimp [e]
      dsimp [Set.prod] at hp ⊢
      simpa [And.comm] using hp
  -- Forward implication
  have forward :
      Topology.P2 (Set.prod A B) → Topology.P2 (Set.prod B A) := by
    intro h
    have h' : Topology.P2 (e '' Set.prod A B) :=
      Topology.P2_image_homeomorph (e := e) (A := Set.prod A B) h
    simpa [h_image_eq] using h'
  -- Backward implication
  have backward :
      Topology.P2 (Set.prod B A) → Topology.P2 (Set.prod A B) := by
    intro h
    have h' : Topology.P2 (e ⁻¹' Set.prod B A) :=
      Topology.P2_preimage_homeomorph (e := e) (B := Set.prod B A) h
    simpa [h_preimage_eq] using h'
  exact ⟨forward, backward⟩

theorem P1_prod_symm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : (Topology.P1 (Set.prod A B) ↔ Topology.P1 (Set.prod B A)) := by
  -- Define the homeomorphism swapping the two factors
  let e := (Homeomorph.prodComm X Y)
  -- The image of `A ×ˢ B` under `e` is `B ×ˢ A`
  have h_image_eq :
      (e '' (Set.prod A B) : Set (Y × X)) = Set.prod B A := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases q with ⟨x, y⟩
      dsimp [e, Homeomorph.prodComm] at *
      dsimp [Set.prod] at hq ⊢
      rcases hq with ⟨hxA, hyB⟩
      exact And.intro hyB hxA
    · intro hp
      rcases p with ⟨y, x⟩
      dsimp [Set.prod] at hp
      rcases hp with ⟨hyB, hxA⟩
      refine ⟨(x, y), ?_, ?_⟩
      · dsimp [Set.prod]
        exact And.intro hxA hyB
      · simp [e, Homeomorph.prodComm]
  -- The preimage of `B ×ˢ A` under `e` is `A ×ˢ B`
  have h_preimage_eq :
      (e ⁻¹' (Set.prod B A) : Set (X × Y)) = Set.prod A B := by
    ext p
    constructor
    · intro hp
      dsimp [Set.preimage, e, Homeomorph.prodComm, Set.prod] at hp
      exact And.intro hp.2 hp.1
    · intro hp
      dsimp [Set.preimage, e, Homeomorph.prodComm, Set.prod]
      exact And.intro hp.2 hp.1
  -- Forward implication
  have forward :
      Topology.P1 (Set.prod A B) → Topology.P1 (Set.prod B A) := by
    intro h
    have h' : Topology.P1 (e '' Set.prod A B) :=
      Topology.P1_image_homeomorph (e := e) (A := Set.prod A B) h
    simpa [h_image_eq] using h'
  -- Backward implication
  have backward :
      Topology.P1 (Set.prod B A) → Topology.P1 (Set.prod A B) := by
    intro h
    have h' : Topology.P1 (e ⁻¹' Set.prod B A) :=
      Topology.P1_preimage_homeomorph (e := e) (B := Set.prod B A) h
    simpa [h_preimage_eq] using h'
  exact ⟨forward, backward⟩

theorem P1_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA : interior A = Set.univ) : Topology.P1 A := by
  dsimp [Topology.P1] at *
  intro x hx
  simpa [hA, interior_univ, closure_univ] using (Set.mem_univ x)