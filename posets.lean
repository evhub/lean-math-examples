import .util

namespace posets
    open function
    open classical (em prop_decidable)
    local attribute [instance] prop_decidable

    open util

    -- comparable:
    inductive comparable {T: Type _} [hT: partial_order T] (x y: T): Prop
    | is_le: x ≤ y → comparable
    | swap_le: y ≤ x → comparable
    open comparable

    theorem le_of_not_lt {T: Type _} [hT: partial_order T] {x y: T} (hxy: comparable x y):
        ¬ x < y →
        y ≤ x := begin
            intro hnlt,
            cases hxy,
            case is_le {
                rw [le_iff_lt_or_eq] at hxy,
                cases hxy,
                case or.inl {
                    contradiction,
                },
                case or.inr {
                    rw [hxy],
                },
            },
            case swap_le {
                exact hxy,
            },
        end

    theorem lt_of_not_le {T: Type _} [hT: partial_order T] {x y: T} (hxy: comparable x y):
        ¬ x ≤ y →
        y < x := begin
            intro hnlt,
            cases hxy,
            case is_le {
                contradiction,
            },
            case swap_le {
                by_contra hnlt,
                have hyx: comparable y x := is_le hxy,
                have hle := le_of_not_lt hyx hnlt,
                contradiction,
            },
        end


    -- bot:
    class has_bot (T: Type _) extends partial_order T :=
        (bot: T)
        (bot_le: ∀ x: T, bot ≤ x)

    @[reducible, inline] def bot {T: Type _} [hT: has_bot T] := hT.bot

    @[reducible, inline] def bot_le {T: Type _} [hT: has_bot T] := hT.bot_le

    instance has_bot.inhabited {T: Type _} [hT: has_bot T]:
        inhabited T := (| bot |)

    theorem bot_uniq {T: Type _} [hT: has_bot T]:
        ∀ bot': T,
        (∀ x: T, bot' ≤ x) →
        bot' = bot := begin
            intros bot' bot_le',
            apply le_antisymm,
            apply bot_le',
            apply bot_le,
        end

    theorem bot_ne_elim {T: Type _} [hT: has_bot T] {x: T}:
        x ≠ bot →
        ∃ y: T,
        ¬ x ≤ y := begin
            intro hne,
            apply not_forall_not_elim,
            intro hnlt,
            apply hne,
            apply bot_uniq,
            intro y,
            have hy := hnlt y,
            simp at hy,
            exact hy,
        end


    -- min:
    noncomputable def or_else {T: Type _} [hT: has_bot T] (x y: T):
        T := if x = bot then y else x

    infix ` ?? `:60 := or_else

    theorem or_else.le_refl {T: Type _} [hT: has_bot T] {x y: T}:
        x ≤ x ?? y := begin
            rw [or_else],
            cases em (x = bot),
            case or.inl {
                rw [if_pos h, h],
                apply bot_le,
            },
            case or.inr {
                rw [if_neg h],
            },
        end

    theorem or_else.le_of_le {T: Type _} [hT: has_bot T] {x y: T}:
        x ≤ y →
        x ≤ y ?? x := begin
            intro hle,
            rw [or_else],
            cases em (y = bot),
            case or.inl {
                rw [if_pos h],
            },
            case or.inr {
                rw [if_neg h],
                exact hle,
            },
        end


    -- max:
    noncomputable def and_then {T: Type _} [hT: has_bot T] (x y: T):
        T := if x = bot then x else y

    infix ` >> `:60 := and_then

    theorem and_then.le_refl {T: Type _} [hT: has_bot T] {x y: T}:
        y >> x ≤ x := begin
            rw [and_then],
            cases em (y = bot),
            case or.inl {
                rw [if_pos h, h],
                apply bot_le,
            },
            case or.inr {
                rw [if_neg h],
            },
        end

    theorem and_then.le_of_le {T: Type _} [hT: has_bot T] {x y: T}:
        x ≤ y →
        y >> x ≤ y := begin
            intro hle,
            rw [and_then],
            cases em (y = bot),
            case or.inl {
                rw [if_pos h],
            },
            case or.inr {
                rw [if_neg h],
                exact hle,
            },
        end


    -- function classes:
    attribute [class] injective
    attribute [class] surjective
    attribute [class] bijective

    instance bijective_of_inj_sur {T T': Sort _} {f: T → T'} [hfi: injective f] [hfs: surjective f]:
        bijective f := (| hfi, hfs |)

    instance inj_of_bijective {T T': Sort _} {f: T → T'} [hf: bijective f]:
        injective f := hf.1

    instance sur_of_bijective {T T': Sort _} {f: T → T'} [hf: bijective f]:
        surjective f := hf.2

    class invertible {T T': Sort _} (f: T → T') :=
        (g: T' → T)
        (elim:
            ∀ x: T,
            g (f x) = x)

    class increasing {T: Type _} [hT: partial_order T] (f: T → T) :=
        (elim:
            ∀ {x: T},
            x ≤ f x)

    class decreasing {T: Type _} [hT: partial_order T] (f: T → T) :=
        (elim:
            ∀ {x: T},
            f x ≤ x)

    class monotone {T T': Type _} [hT: partial_order T] [hT': partial_order T'] (f: T → T') :=
        (elim:
            ∀ {x y: T},
            x ≤ y →
            f x ≤ f y)

    class antitone {T T': Type _} [hT: partial_order T] [hT': partial_order T'] (f: T → T') :=
        (elim:
            ∀ {x y: T},
            f x ≤ f y →
            x ≤ y)


    -- inverses:
    @[reducible, inline] def inv {T T': Sort _} (f: T → T') [hf: invertible f]:
        T' → T := hf.g

    @[simp] theorem inv.elim {T T': Sort _} (f: T → T') [hf: invertible f]:
        ∀ x: T,
        inv f (f x) = x := by apply hf.elim

    instance inv.invertible {T T': Sort _} (f: T → T') [hfinv: invertible f] [hfsur: surjective f]:
        invertible (inv f) := begin
            split,
            show T → T', from f,
            intro x,
            apply exists.elim (hfsur x),
            intros y hy,
            rw [←hy],
            simp,
        end

    theorem inv.uniq {T T': Sort _} (f: T → T') [hfinv: invertible f] [hfsur: surjective f]:
        ∀ {g: T' → T},
        (∀ x: T, g (f x) = x) →
        g = inv f := begin
            intros g hg,
            funext,
            have hfsurx := hfsur x,
            apply exists.elim hfsurx,
            intros y hy,
            rw [←hy, hg y],
            rw [inv, hfinv.elim],
        end


    -- id:
    instance id.bijective {T: Sort _}:
        bijective (@id T) := begin
            split,
            show injective id, by {
                intros x y h,
                simp at h,
                exact h,
            },
            show surjective id, by {
                intro x,
                apply exists.intro x,
                simp,
            },
        end

    instance id.increasing {T: Type _} [hT: partial_order T]:
        increasing (@id T) := begin
            split,
            intro x,
            simp,
        end

    instance id.decreasing {T: Type _} [hT: partial_order T]:
        decreasing (@id T) := begin
            split,
            intro x,
            simp,
        end

    instance id.monotone {T: Type _} [hT: partial_order T]:
        monotone (@id T) := begin
            split,
            intros x y hxy,
            simp,
            exact hxy,
        end

    instance id.antitone {T: Type _} [hT: partial_order T]:
        antitone (@id T) := begin
            split,
            intros x y hid,
            simp at hid,
            exact hid,
        end

    instance id.invertible {T: Sort _}:
        invertible (@id T) := begin
            split,
            show T → T, from id,
            intro x,
            simp,
        end


    -- monotonicity:
    @[simp] theorem monotone.bot_to_bot_of_sur {T T': Type _} [hT: has_bot T] [hT': has_bot T'] (f: T → T') [hfm: monotone f] [hfs: surjective f]:
        f bot = bot := begin
            apply bot_uniq,
            intro x,
            have hfsx := hfs x,
            apply exists.elim hfsx,
            intros y hy,
            rw [←hy],
            apply hfm.elim,
            apply bot_le,
        end

    instance monotone.cod_has_bot_of_sur {T T': Type _} [hT: has_bot T] [hT': partial_order T'] (f: T → T') [hfm: monotone f] [hfs: surjective f]:
        has_bot T' := begin
            split,
            show T', from f bot,
            intro x,
            have hfsx := hfs x,
            apply exists.elim hfsx,
            intros y hy,
            rw [←hy],
            apply hfm.elim,
            apply bot_le,
        end

    instance monotone.of_comp {T T' T'': Type _} [hT: partial_order T] [hT': partial_order T'] [hT'': partial_order T''] (g: T → T') [hg: monotone g] (f: T' → T'') [hf: monotone f]:
        monotone (f ∘ g) := begin
            split,
            intros x y hxy,
            simp,
            apply hf.elim,
            apply hg.elim,
            exact hxy,
        end


    -- galois connections:
    structure galois_connection (A B: Type _) [hA: partial_order A] [hB: partial_order B] :=
        (F: A → B)
        [hF: monotone F]
        (G: B → A)
        [hG: monotone G]
        (elim:
            ∀ {a: A} {b: B},
            F a ≤ b ↔
            a ≤ G b)

    def galois_connection.closure {A B: Type _} [hA: partial_order A] [hB: partial_order B] (gc: galois_connection A B):
        A → A := gc.G ∘ gc.F

    instance galois_connection.closure.monotone {A B: Type _} [hA: partial_order A] [hB: partial_order B] (gc: galois_connection A B):
        monotone gc.closure := by apply @monotone.of_comp A B A hA hB hA gc.F gc.hF gc.G gc.hG

    def galois_connection.kernel {A B: Type _} [hA: partial_order A] [hB: partial_order B] (gc: galois_connection A B):
        B → B := gc.F ∘ gc.G

    instance galois_connection.kernel.monotone {A B: Type _} [hA: partial_order A] [hB: partial_order B] (gc: galois_connection A B):
        monotone gc.kernel := by apply @monotone.of_comp B A B hB hA hB gc.G gc.hG gc.F gc.hF
end posets
