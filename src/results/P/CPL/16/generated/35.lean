

theorem P1_prod_swap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P1 (Set.prod A B) → P1 (Set.prod B A) := by
  intro hP1
  -- Unfold the definition of `P1`
  unfold P1 at hP1 ⊢
  intro p hpBA
  -- `q` is the point obtained by swapping the coordinates of `p`
  have hq_closure : ((p.2, p.1) : X × Y) ∈ closure (interior (Set.prod A B)) := by
    have hq_mem : ((p.2, p.1) : X × Y) ∈ Set.prod A B := by
      exact ⟨hpBA.2, hpBA.1⟩
    exact hP1 hq_mem
  -- We prove that `p` belongs to the required closure using the
  -- neighbourhood characterization.
  apply (mem_closure_iff).2
  intro U hU hpU
  -- `V` is the preimage of `U` by the swap map, it is an open set
  -- containing `q`.
  let V : Set (X × Y) := {q | Prod.swap q ∈ U}
  have hV_open : IsOpen V := by
    have h_cont : Continuous fun q : X × Y => Prod.swap q := continuous_swap
    have : IsOpen ((fun q : X × Y => Prod.swap q) ⁻¹' U) := hU.preimage h_cont
    simpa [V] using this
  have hqV : ((p.2, p.1) : X × Y) ∈ V := by
    dsimp [V]
    have h_eq : Prod.swap (p.2, p.1) = p := by
      cases p
      simp [Prod.swap]
    simpa [h_eq] using hpU
  -- Since `q` is in the closure, `V` meets `interior (A ×ˢ B)`.
  have h_nonempty : (V ∩ interior (Set.prod A B)).Nonempty := by
    have := (mem_closure_iff).1 hq_closure V hV_open hqV
    simpa [Set.inter_comm] using this
  rcases h_nonempty with ⟨w, hwV, hwIntAB⟩
  -- `w' = swap w` will lie in `U ∩ interior (B ×ˢ A)`.
  have hwU : Prod.swap w ∈ U := by
    dsimp [V] at hwV
    exact hwV
  -- Show that `Prod.swap w` is in the interior of `B ×ˢ A`.
  have hwIntBA : Prod.swap w ∈ interior (Set.prod B A) := by
    -- Auxiliary open set whose image is contained in `B ×ˢ A`.
    let U₂ : Set (Y × X) := {x | Prod.swap x ∈ interior (Set.prod A B)}
    have hU₂_open : IsOpen U₂ := by
      have h_cont : Continuous fun x : Y × X => Prod.swap x := continuous_swap
      have : IsOpen ((fun x : Y × X => Prod.swap x) ⁻¹' interior (Set.prod A B)) :=
        isOpen_interior.preimage h_cont
      simpa [U₂] using this
    have hU₂_sub : (U₂ : Set (Y × X)) ⊆ Set.prod B A := by
      intro x hx
      dsimp [U₂] at hx
      have h_swap_mem : Prod.swap x ∈ Set.prod A B := interior_subset hx
      rcases x with ⟨y, x'⟩
      dsimp [Prod.swap] at h_swap_mem
      rcases h_swap_mem with ⟨hx'A, hyB⟩
      exact ⟨hyB, hx'A⟩
    have h_mem_U₂ : Prod.swap w ∈ U₂ := by
      dsimp [U₂]
      have h_eq : Prod.swap (Prod.swap w) = w := by
        cases w
        simp [Prod.swap]
      simpa [h_eq] using hwIntAB
    have h_subset := interior_maximal hU₂_sub hU₂_open
    exact h_subset h_mem_U₂
  -- `Prod.swap w` witnesses the required non-emptiness.
  exact ⟨Prod.swap w, hwU, hwIntBA⟩

theorem P2_prod_swap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P2 (Set.prod A B) → P2 (Set.prod B A) := by
  intro hP2
  -- Unfold the definition of `P2`
  unfold P2 at hP2 ⊢
  intro p hpBA
  -- `p` lives in `B ×ˢ A`, hence its swap lives in `A ×ˢ B`
  have h_swap_mem : Prod.swap p ∈ Set.prod A B := by
    rcases hpBA with ⟨hpB, hpA⟩
    exact ⟨hpA, hpB⟩
  -- Use the hypothesis on the swapped point
  have h_swap_int :
      Prod.swap p ∈ interior (closure (interior (Set.prod A B))) :=
    hP2 h_swap_mem
  -- Define an auxiliary open set `S`
  let S : Set (Y × X) :=
      {q | Prod.swap q ∈ interior (closure (interior (Set.prod A B)))}
  have hS_open : IsOpen (S : Set (Y × X)) := by
    have : IsOpen
        ((fun q : Y × X => Prod.swap q) ⁻¹'
          interior (closure (interior (Set.prod A B)))) :=
      (isOpen_interior).preimage continuous_swap
    simpa [S] using this
  have hpS : p ∈ S := by
    dsimp [S]
    simpa using h_swap_int
  -- Show that `S ⊆ closure (interior (B ×ˢ A))`
  have hS_subset :
      (S : Set (Y × X)) ⊆ closure (interior (Set.prod B A)) := by
    intro z hz
    -- Information carried by `hz`
    have hz_swap :
        Prod.swap z ∈ interior (closure (interior (Set.prod A B))) := by
      dsimp [S] at hz
      exact hz
    have hz_clos :
        Prod.swap z ∈ closure (interior (Set.prod A B)) :=
      (interior_subset) hz_swap
    -- Prove that `z` belongs to the required closure
    apply (mem_closure_iff).2
    intro U hU hzU
    -- Preimage of `U` under `Prod.swap`
    let V : Set (X × Y) := {q | Prod.swap q ∈ U}
    have hV_open : IsOpen (V : Set (X × Y)) := by
      have : IsOpen ((fun q : X × Y => Prod.swap q) ⁻¹' U) :=
        hU.preimage continuous_swap
      simpa [V] using this
    have hzV : Prod.swap z ∈ V := by
      dsimp [V] ; simpa using hzU
    -- Since `Prod.swap z` is in the closure, `V` meets `interior (A ×ˢ B)`
    have h_nonempty :
        (V ∩ interior (Set.prod A B)).Nonempty := by
      have := (mem_closure_iff).1 hz_clos V hV_open hzV
      simpa [Set.inter_comm] using this
    rcases h_nonempty with ⟨w, hwV, hwIntAB⟩
    -- `Prod.swap w` lies in `U`
    have hwU : Prod.swap w ∈ U := by
      dsimp [V] at hwV ; exact hwV
    -- Show that `Prod.swap w` is in `interior (B ×ˢ A)`
    have hwIntBA : Prod.swap w ∈ interior (Set.prod B A) := by
      -- Auxiliary set to transport interior through the swap
      let U₂ : Set (Y × X) := {x | Prod.swap x ∈ interior (Set.prod A B)}
      have hU₂_open : IsOpen (U₂ : Set (Y × X)) := by
        have : IsOpen ((fun x : Y × X => Prod.swap x) ⁻¹'
            interior (Set.prod A B)) :=
          (isOpen_interior).preimage continuous_swap
        simpa [U₂] using this
      have hU₂_sub : (U₂ : Set (Y × X)) ⊆ Set.prod B A := by
        intro x hx
        dsimp [U₂] at hx
        have h_swap_mem : Prod.swap x ∈ Set.prod A B := interior_subset hx
        rcases x with ⟨y, x'⟩
        dsimp [Prod.swap] at h_swap_mem
        rcases h_swap_mem with ⟨hx'A, hyB⟩
        exact ⟨hyB, hx'A⟩
      have h_mem_U₂ : Prod.swap w ∈ U₂ := by
        dsimp [U₂]
        have : Prod.swap (Prod.swap w) = w := by
          cases w ; simp [Prod.swap]
        simpa [this] using hwIntAB
      exact (interior_maximal hU₂_sub hU₂_open) h_mem_U₂
    -- Provide the witness in `U ∩ interior (B ×ˢ A)`
    exact ⟨Prod.swap w, hwU, hwIntBA⟩
  -- Conclude using `interior_maximal`
  have hp_int :
      p ∈ interior (closure (interior (Set.prod B A))) :=
    (interior_maximal hS_subset hS_open) hpS
  exact hp_int

theorem P3_prod_swap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P3 (Set.prod A B) → P3 (Set.prod B A) := by
  intro hP3
  -- unfold the definition of `P3`
  unfold P3 at hP3 ⊢
  intro p hpBA
  -- the swapped point lives in `A ×ˢ B`
  have h_swap_mem : Prod.swap p ∈ Set.prod A B := by
    rcases hpBA with ⟨hpB, hpA⟩
    exact ⟨hpA, hpB⟩
  -- apply the hypothesis to the swapped point
  have h_swap_int : Prod.swap p ∈ interior (closure (Set.prod A B)) :=
    hP3 h_swap_mem
  -- define an auxiliary open set
  let S : Set (Y × X) := {q | Prod.swap q ∈ interior (closure (Set.prod A B))}
  have hS_open : IsOpen (S : Set (Y × X)) := by
    have :
        IsOpen
          ((fun q : Y × X => Prod.swap q) ⁻¹'
            interior (closure (Set.prod A B))) :=
      (isOpen_interior).preimage continuous_swap
    simpa [S] using this
  have hpS : p ∈ S := by
    dsimp [S]
    simpa using h_swap_int
  -- show that `S ⊆ closure (B ×ˢ A)`
  have hS_subset : (S : Set (Y × X)) ⊆ closure (Set.prod B A) := by
    intro z hz
    -- information on `Prod.swap z`
    have hz_swap :
        Prod.swap z ∈ interior (closure (Set.prod A B)) := by
      dsimp [S] at hz
      exact hz
    have hz_clos :
        Prod.swap z ∈ closure (Set.prod A B) :=
      interior_subset hz_swap
    -- neighbourhood characterization of the closure
    apply (mem_closure_iff).2
    intro U hU hzU
    -- preimage of `U` under the swap map
    let V : Set (X × Y) := {q | Prod.swap q ∈ U}
    have hV_open : IsOpen (V : Set (X × Y)) := by
      have : IsOpen ((fun q : X × Y => Prod.swap q) ⁻¹' U) :=
        hU.preimage continuous_swap
      simpa [V] using this
    have hzV : Prod.swap z ∈ V := by
      dsimp [V] ; simpa using hzU
    -- `V` meets `A ×ˢ B`
    have h_nonempty : (V ∩ Set.prod A B).Nonempty := by
      have := (mem_closure_iff).1 hz_clos V hV_open hzV
      simpa [Set.inter_comm] using this
    rcases h_nonempty with ⟨w, hwV, hwAB⟩
    -- the swapped point belongs to `U ∩ (B ×ˢ A)`
    have hwU : Prod.swap w ∈ U := by
      dsimp [V] at hwV
      exact hwV
    have hwBA : Prod.swap w ∈ Set.prod B A := by
      rcases w with ⟨a, b⟩
      dsimp [Prod.swap] at *
      rcases hwAB with ⟨haA, hbB⟩
      exact ⟨hbB, haA⟩
    exact ⟨Prod.swap w, hwU, hwBA⟩
  -- conclude using `interior_maximal`
  exact (interior_maximal hS_subset hS_open) hpS