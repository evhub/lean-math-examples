import .util

namespace posets
    open function
    open classical (em prop_decidable)
    local attribute [instance] prop_decidable

    open util

    -- comparable:
    inductive comp {T: Sort _} [hT: partial_order T] (x y: T): Prop
    | le (hle: x ≤ y): comp
    | ge (hge: y ≤ x): comp

    infix ` <=> `:50 := comp

    @[refl] theorem comp.refl {T: Sort _} [hT: partial_order T] (x: T):
        x <=> x := begin
            apply comp.le,
            refl,
        end

    @[symm] theorem comp.symm {T: Sort _} [hT: partial_order T] {x y: T}:
        x <=> y →
        y <=> x := begin
            intro hcomp,
            induction hcomp,
            case comp.le {
                apply comp.ge,
                exact hcomp,
            },
            case comp.ge {
                apply comp.le,
                exact hcomp,
            },
        end

    theorem le_of_not_lt {T: Sort _} [hT: partial_order T] {x y: T} (hcomp: x <=> y):
        ¬ x < y →
        y ≤ x := begin
            intro hnlt,
            cases hcomp,
            case comp.le {
                rw [le_iff_lt_or_eq] at hcomp,
                cases hcomp,
                case or.inl {
                    contradiction,
                },
                case or.inr {
                    rw [hcomp],
                },
            },
            case comp.ge {
                exact hcomp,
            },
        end

    theorem lt_of_not_le {T: Sort _} [hT: partial_order T] {x y: T} (hcomp: x <=> y):
        ¬ x ≤ y →
        y < x := begin
            intro hnlt,
            cases hcomp,
            case comp.le {
                contradiction,
            },
            case comp.ge {
                by_contra hnlt,
                have hyx: comp y x := comp.le hcomp,
                have hle := le_of_not_lt hyx hnlt,
                contradiction,
            },
        end


    -- connectedness:
    inductive con {T: Sort _} [hT: partial_order T]: T → T → Prop
    | le {x y: T} (hle: x ≤ y): con x y
    | ge {x y: T} (hge: y ≤ x): con x y
    | trans {x y z: T} (hxy: con x y) (hyz: con y z): con x z

    infix ` ~ ` := con

    @[refl] theorem con.refl {T: Sort _} [hT: partial_order T] (x: T):
        x ~ x := begin
            intros,
            apply con.le,
            refl,
        end

    @[symm] theorem con.symm {T: Sort _} [hT: partial_order T] {x y: T}:
        x ~ y →
        y ~ x := begin
            intro hcon,
            induction hcon,
            case con.le {
                apply con.ge,
                assumption,
            },
            case con.ge {
                apply con.le,
                assumption,
            },
            case con.trans {
                exact con.trans hcon_ih_hyz hcon_ih_hxy,
            },
        end

    theorem comp.con {T: Sort _} [hT: partial_order T] {x y: T} (hcomp: x <=> y):
        x ~ y := begin
            induction hcomp,
            case comp.le {
                apply con.le,
                exact hcomp,
            },
            case comp.ge {
                apply con.ge,
                exact hcomp,
            },
        end


    -- well-founded order:
    class wf_order (T: Sort _) extends partial_order T :=
        (bot: T)
        (bot_le: ∀ x: T, bot ≤ x)

    @[reducible, inline] def bot {T: Sort _} [hT: wf_order T] := hT.bot

    @[reducible, inline] def bot_le {T: Sort _} [hT: wf_order T] := hT.bot_le

    instance wf_order.inhabited {T: Sort _} [hT: wf_order T]:
        inhabited T := (| bot |)

    theorem bot_uniq {T: Sort _} [hT: wf_order T]:
        ∀ bot': T,
        (∀ x: T, bot' ≤ x) →
        bot' = bot := begin
            intros bot' bot_le',
            apply le_antisymm,
            apply bot_le',
            apply bot_le,
        end

    theorem bot_ne_elim {T: Sort _} [hT: wf_order T] {x: T}:
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

    theorem con.all_of_bot {T: Sort _} [hT: wf_order T] {x y: T}:
        x ~ y := begin
            have hx: x ~ bot, by {
                apply con.ge,
                apply bot_le,
            },
            have hy: bot ~ y, by {
                apply con.le,
                apply bot_le,
            },
            exact con.trans hx hy,
        end


    -- trivial order:
    @[reducible] def trivially_ordered (T: Sort _) [hT: partial_order T]: Prop :=
        ∀ {x y: T},
        x ≤ y → x = y

    @[simp] theorem trivially_ordered.elim {T: Sort _} [hT: partial_order T] (htriv: trivially_ordered T):
        ∀ {x y: T},
        x ≤ y ↔ x = y := begin
            intros,
            apply iff.intro,
            {
                intro h,
                exact htriv h,
            },
            {
                intro h,
                rw [h],
            },
        end

    @[simp] theorem trivially_ordered.of_wf {T: Sort _} [hT: wf_order T] (htriv: trivially_ordered T):
        ∀ {x: T},
        x = bot := begin
            intros,
            symmetry,
            apply htriv,
            apply bot_le,
        end

    -- not marked as instance to avoid automatically trivially ordering everything
    def trivial_ordering (T: Sort _):
        partial_order T := {
            le := eq,
            le_refl := begin
                intros,
                refl,
            end,
            le_trans := begin
                intros x y z hxy hyz,
                rw [hxy, ←hyz],
            end,
            le_antisymm := begin
                intros,
                assumption,
            end,
        }

    theorem trivial_ordering.is_triv (T: Sort _):
        @trivially_ordered T (trivial_ordering T) := begin
            intros x y,
            intro hxy,
            cases hxy,
            refl,
        end


    -- min:
    noncomputable def or_else {T: Sort _} [hT: wf_order T] (x y: T):
        T := if x = bot then y else x

    infix ` ?? `:60 := or_else

    theorem or_else.le_refl {T: Sort _} [hT: wf_order T] {x y: T}:
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

    theorem or_else.le_of_le {T: Sort _} [hT: wf_order T] {x y: T}:
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
    noncomputable def and_then {T: Sort _} [hT: wf_order T] (x y: T):
        T := if x = bot then x else y

    infix ` >> `:60 := and_then

    theorem and_then.le_refl {T: Sort _} [hT: wf_order T] {x y: T}:
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

    theorem and_then.le_of_le {T: Sort _} [hT: wf_order T] {x y: T}:
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
    class increasing {T: Sort _} [hT: partial_order T] (f: T → T) :=
        (elim:
            ∀ {x: T},
            x ≤ f x)

    class decreasing {T: Sort _} [hT: partial_order T] (f: T → T) :=
        (elim:
            ∀ {x: T},
            f x ≤ x)

    class monotone {T T': Sort _} [hT: partial_order T] [hT': partial_order T'] (f: T → T') :=
        (elim:
            ∀ {x y: T},
            x ≤ y →
            f x ≤ f y)

    class antitone {T T': Sort _} [hT: partial_order T] [hT': partial_order T'] (f: T → T') :=
        (elim:
            ∀ {x y: T},
            f x ≤ f y →
            x ≤ y)


    -- id:
    instance id.increasing {T: Sort _} [hT: partial_order T]:
        increasing (@id T) := begin
            split,
            intro x,
            simp,
        end

    instance id.decreasing {T: Sort _} [hT: partial_order T]:
        decreasing (@id T) := begin
            split,
            intro x,
            simp,
        end

    instance id.monotone {T: Sort _} [hT: partial_order T]:
        monotone (@id T) := begin
            split,
            intros x y hxy,
            simp,
            exact hxy,
        end

    instance id.antitone {T: Sort _} [hT: partial_order T]:
        antitone (@id T) := begin
            split,
            intros x y hid,
            simp at hid,
            exact hid,
        end


    -- monotonicity:
    theorem monotone.of_comparable {T T': Sort _} [hT: partial_order T] [hT': partial_order T'] {f: T → T'} [hf: monotone f]:
        ∀ {x y: T},
        x <=> y →
        f x <=> f y := begin
            intros x y hcomp,
            induction hcomp,
            case comp.le {
                apply comp.le,
                apply hf.elim,
                exact hcomp,
            },
            case comp.ge {
                apply comp.ge,
                apply hf.elim,
                exact hcomp,
            },
        end

    theorem monotone.of_con {T T': Sort _} [hT: partial_order T] [hT': partial_order T'] {f: T → T'} [hf: monotone f]:
        ∀ {x y: T},
        x ~ y →
        f x ~ f y := begin
            intros x y hcon,
            induction hcon,
            case con.le {
                apply con.le,
                apply hf.elim,
                assumption,
            },
            case con.ge {
                apply con.ge,
                apply hf.elim,
                assumption,
            },
            case con.trans {
                exact con.trans hcon_ih_hxy hcon_ih_hyz,
            },
        end

    @[simp] theorem monotone.bot_to_bot_of_sur {T T': Sort _} [hT: wf_order T] [hT': wf_order T'] (f: T → T') [hfm: monotone f] [hfs: surjective f]:
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

    instance monotone.cod_wf_order_of_sur {T T': Sort _} [hT: wf_order T] [hT': partial_order T'] (f: T → T') [hfm: monotone f] [hfs: surjective f]:
        wf_order T' := begin
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

    instance monotone.of_composition {T T' T'': Sort _} [hT: partial_order T] [hT': partial_order T'] [hT'': partial_order T''] (g: T → T') [hg: monotone g] (f: T' → T'') [hf: monotone f]:
        monotone (f ∘ g) := begin
            split,
            intros x y hxy,
            simp,
            apply hf.elim,
            apply hg.elim,
            exact hxy,
        end


    -- galois connections:
    structure galois_connection (A B: Sort _) [hA: partial_order A] [hB: partial_order B] :=
        (F: A → B)
        [hF: monotone F]
        (G: B → A)
        [hG: monotone G]
        (elim:
            ∀ {a: A} {b: B},
            F a ≤ b ↔
            a ≤ G b)

    def galois_connection.closure {A B: Sort _} [hA: partial_order A] [hB: partial_order B] (gc: galois_connection A B):
        A → A := gc.G ∘ gc.F

    instance galois_connection.closure.monotone {A B: Sort _} [hA: partial_order A] [hB: partial_order B] (gc: galois_connection A B):
        monotone gc.closure := by apply @monotone.of_composition A B A hA hB hA gc.F gc.hF gc.G gc.hG

    def galois_connection.kernel {A B: Sort _} [hA: partial_order A] [hB: partial_order B] (gc: galois_connection A B):
        B → B := gc.F ∘ gc.G

    instance galois_connection.kernel.monotone {A B: Sort _} [hA: partial_order A] [hB: partial_order B] (gc: galois_connection A B):
        monotone gc.kernel := by apply @monotone.of_composition B A B hB hA hB gc.G gc.hG gc.F gc.hF
end posets
