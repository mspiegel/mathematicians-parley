//! Requires lines, kinds and the families they ask.

use std::slice;

use super::*;
use crate::corpus::proof;
use crate::methods::membership;

/// A requires line needs what the item it cites concludes.
///
/// A step's citation is matched this way already. A requires line carries
/// the same kind of pointer to the same kind of item, and was checked only
/// for resolving, so an item that did not cover the fact went unnoticed.
pub fn check_requires(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
) {
    for step in &thm.steps {
        for found in unconcluded(step, known, library) {
            let said = match &found.missing {
                Some(missing) => format!(
                    "the requires line of {} cites {}, which asks for {}, and what it cites does not supply {}",
                    step.called(),
                    found.item,
                    missing.join("; "),
                    if missing.len() == 1 { "it" } else { "them" }
                ),
                None => format!(
                    "the requires line of {} needs something that {} does not conclude",
                    step.called(),
                    found.item
                ),
            };
            report.say(&thm.path, found.line, said);
        }
    }
}

/// A let saying what kind of number its name is gives the reason on the
/// line under it, and the reason shows the term the let names is one, as a
/// requires line's reason shows its fact: it is read as a requires line of
/// the step below the let, whose scope the let stands in (`SYNTAX.md`,
/// naming a thing).
pub fn check_kinds(
    report: &mut Report,
    thm: &Theorem,
    library: &Library,
    known: &Known,
) {
    for d in &thm.defines {
        let kinded = match d.kinded(&thm.path, &known.env.g.members) {
            Ok(Some(kinded)) => kinded,
            Ok(None) => continue,
            Err(problem) => {
                report.problems.push(problem);
                continue;
            }
        };
        let Some(after) = thm.step_after(d.line) else {
            report.say(
                &thm.path,
                d.line,
                format!(
                    "let {} stands below every step, where no step uses it",
                    d.label
                ),
            );
            continue;
        };
        let Some(reason) = d.reason.as_ref() else {
            continue;
        };
        // The let's requires lines are checked as a step's are
        // (`check_let_requires`); here they are what the reason rests on.
        let under = reason.under(&d.label, after, kinded.shown.fact.clone());
        let unshown = unconcluded(&under, known, library)
            .into_iter()
            .filter(|found| found.line == reason.line);
        for found in unshown {
            let said = match &found.missing {
                Some(missing) => format!(
                    "the reason under let {} cites {}, which asks for {}, and what it cites does not supply {}",
                    d.label,
                    found.item,
                    missing.join("; "),
                    if missing.len() == 1 { "it" } else { "them" }
                ),
                None => format!(
                    "the reason under let {} needs {}, which {} does not conclude",
                    d.label, kinded.shown.fact, found.item
                ),
            };
            report.say(&thm.path, found.line, said);
        }
    }
}

/// Whether a requires line below `req` in its step rests on what `req` says
/// is a member, or not zero, by a method that asks it of its atoms and the
/// terms it divides by (`METHODS.md`): `requires |PQ| ∈ ℝ` above `requires
/// |PQ|·|P′R′| ∈ ℝ: membership`, `requires d ∈ ℝ` above `requires 0 < d:
/// inequalities, from 3.1`, or `requires b − a ≠ 0` above `requires (f(a) −
/// f(b))/(b − a) ∈ ℝ: membership`. An order between terms is what
/// `inequalities` reasons from, so `requires sin(∠PQR) > 0` is asked for by
/// `requires sin(∠PQR) ≠ 0: inequalities` below it. An equation names both
/// its sides, so `requires deg(u) = |S|` is asked for by `requires deg(u) ∈
/// ℤ: membership` below it. The term may reach the line below through a line
/// it cites or another requires line above it, as `requires deg(x) ∈ ℕ₀:
/// membership, from 2` rests on `requires |S| ∈ ℕ₀` where line 2 says deg(x)
/// = |S|. Such a line is asked for as surely as an item's hypothesis is
/// (`SYNTAX.md`: a requires line rests on the lines above it).
pub(super) fn built_on(req: &Requires, step: &Step, known: &Known) -> bool {
    const ASKING: [Method; 3] =
        [Method::Membership, Method::Inequalities, Method::Algebra];
    let Some(said) = known.whole(step, &req.fact) else {
        return false;
    };
    // t ∈ X names t: a method asks it of its atoms. t ≠ 0, read as not
    // t = 0, names t, which `membership` and `algebra` ask of a divisor, and
    // says it written either way round, 0 ≠ t as well; `inequalities` takes
    // two terms differing only from a line it cites, not from one above
    // (`METHODS.md`). t < u names both sides, and only `inequalities` reads
    // an order. t = u names both sides too, and a line below may say of one
    // what it says of the other, so there a term the line below holds whole
    // is one it rests on.
    let (held, asking, whole): (Vec<&Node>, &[Method], bool) = match said.notation() {
        MEMBERSHIP if said.children.len() == 2 => {
            (vec![&said.children[0]], &ASKING, false)
        }
        LOGICAL_NOT
            if said.children.len() == 1
                && said.children[0].notation() == EQUALITY
                && said.children[0].children.len() == 2 =>
        {
            (
                said.children[0]
                    .children
                    .iter()
                    .filter(|c| c.notation() != NUMERAL)
                    .collect(),
                &[Method::Membership, Method::Algebra],
                false,
            )
        }
        ORDER if said.children.len() == 2 => (
            said.children
                .iter()
                .filter(|c| c.notation() != NUMERAL)
                .collect(),
            &[Method::Inequalities],
            false,
        ),
        EQUALITY if said.children.len() == 2 => (
            said.children
                .iter()
                .filter(|c| c.notation() != NUMERAL)
                .collect(),
            &ASKING,
            true,
        ),
        _ => return false,
    };
    let atoms: Vec<&Node> = held;
    let holds_atom = |n: &Node| {
        atoms
            .iter()
            .any(|atom| n.walk().iter().any(|part| part.spelt_alike(atom)))
    };
    let scope = known.scope(step);
    step.requires
        .iter()
        .skip_while(|r| r.line != req.line)
        .skip(1)
        .filter(|r| {
            // A manipulation, `weakening, from 8`, is a row of `inequalities`
            // and asks its atoms real as that method does.
            let manipulated = asking.contains(&Method::Inequalities)
                && matches!(&r.by, Ok(by) if matches!(by.head, Head::Manipulation(_)));
            manipulated || asking.iter().any(|m| r.is(*m))
        })
        .filter_map(|r| known.whole(step, &r.fact).map(|n| (r, n)))
        .any(|(r, n)| {
            let held = if n.notation() == MEMBERSHIP && n.children.len() == 2 {
                &n.children[0]
            } else {
                &n
            };
            let written = atoms.iter().any(|atom| {
                (whole || !held.spelt_alike(atom))
                    && held.walk().iter().any(|part| part.spelt_alike(atom))
            });
            // Or it holds the term once the defines it cites are written
            // out: `U(0) ∈ ℝ: membership, from D6` divides by 10^0, which
            // D6's U(k) = (N(k) + 1)/10^k makes of U(0).
            let lower = known.citing_item(r.lines(), None);
            let defined_out = r
                .fact
                .sentences()
                .iter()
                .filter_map(|s| known.read_citing(s, &lower))
                .any(|line| holds_atom(&line));
            // A line the lower one cites, or another requires line above it,
            // carries the term to it: `deg(x) ∈ ℕ₀: membership, from 2` rests
            // on `|S| ∈ ℕ₀` above it where line 2 says deg(x) = |S|, and so
            // does `deg(x) ∈ ℤ: membership` under `requires deg(x) = |S|`.
            let defined = known.citing_step(step);
            let cited = r
                .lines()
                .iter()
                .filter_map(|c| scope.get(c))
                .flat_map(|written| known.supplied(written, &defined))
                .any(|line| holds_atom(&line));
            let above = step
                .requires
                .iter()
                .take_while(|o| o.line != r.line)
                .filter(|o| o.line != req.line)
                .flat_map(|o| known.said(step, &o.fact))
                .any(|line| holds_atom(&line));
            written || defined_out || cited || above
        })
}

/// The requires lines a cited item's function hypotheses ask for.
///
/// `let t : {a, …, b} → ℝ` in a sum item, where the step's summand is what t
/// stands for, says every term is real. That is not a line the page writes:
/// the terms are built from numbers the step names, and the elaborator
/// builds each term's membership from theirs, as `algebra` builds a
/// compound's from its atoms'. So what the hypothesis asks is the membership
/// of each name the summand holds that the sum does not bind: C(m, k)·x^(m −
/// k)·y^k asks x ∈ ℝ, y ∈ ℝ and m ∈ ℕ₀, and nothing of k.
///
/// `let g : D → ℝ` where g stands for a function the proof defines asks
/// what g maps between, said whole and as the item says it: `g := g, D :=
/// [a, b]` asks g : [a, b] → ℝ and nothing else of g. The checker reads the
/// define as its rule, and the kernel asks it of every value the rule gives.
pub(super) struct FamilyAsks {
    pub(super) held: BTreeSet<String>,
    pub(super) values: Vec<Node>,
    pub(super) types: Vec<AskedType>,
    /// The item's function types the citation asks of functions a `let`
    /// declares, whose types are not asked for and whose codomains are.
    pub(super) declared_types: Vec<AskedType>,
    /// The number systems the page says once its letters are in at the
    /// step, which with `in_scope` say whether a term's divisor is a
    /// positive integer.
    pub(super) letters: Introduced,
    /// The function types in scope at the step, which say a function's
    /// value is in its codomain at a point of its domain.
    pub(super) in_scope: Vec<Node>,
    /// Which notations bind, so that a value is compared up to the letters
    /// it binds.
    pub(super) ctx: Context,
}

/// A function type an item asks of a citation, under what the citation
/// writes for its letters.
pub(super) struct AskedType {
    /// `F : D → E` for the item's `let f : D → E` at `f := F`.
    pub(super) asked: Node,
    /// The item's letters among its sets that the citation leaves unfilled,
    /// which the line stating the type fills: D and E above.
    pub(super) open: BTreeSet<String>,
    /// Whether the citation says what the item's function stands for, so
    /// that the type is asked of one of the page's functions.
    pub(super) filled: bool,
    /// What the match of the citation makes the function where it is a
    /// rule, a sum's summand `k ↦ 1/T(k)` for the item's t.
    pub(super) rule: Option<Node>,
}

impl AskedType {
    /// The term a sum's function hypothesis asks at every point and the
    /// letter it is asked at: `1/T(k)` and k, of `t : {1, …, n} → ℝ` where
    /// the citation makes t the summand. None for a type the citation
    /// fills with a named function.
    pub(super) fn pointwise(&self) -> Option<(&str, &Node)> {
        let f = self.asked.children.first()?;
        let f = if f.notation() == PROPERTY_OF {
            f
        } else {
            self.rule.as_ref()?
        };
        Some((f.text.as_str(), f.children.first()?))
    }

    /// Whether the term the type asks at every point must be said there: it
    /// divides by something holding the type's letter that the page does
    /// not say once is a positive integer, `letters` its letters, as 1/T(k)
    /// and 1/(k(k + 1)/2) do. A divisor's `≠ 0` is written there
    /// (`SYNTAX.md`), and no line outside the sum can speak of its letter,
    /// so the term is said at every point by a line the citation names.
    pub(super) fn needs_saying(&self, given: &membership::Facts) -> bool {
        let (Some((letter, term)), Some(domain)) =
            (self.pointwise(), self.asked.children.get(1))
        else {
            return false;
        };
        let inside = match domain.notation() {
            INTEGER_RANGE => range_system(domain),
            NUMBER_SYSTEMS => System::of_sign(&domain.text),
            _ => None,
        };
        membership::divides_by(term, letter, inside, given)
    }

    /// The sums inside the term the type asks at every point whose own
    /// term divides by their index as `needs_saying` reads it, `given` the
    /// page's letters and types in scope: Σ(k = 1 to n) 1/T(k) inside
    /// `x : ℕ → ℝ` at x := n ↦ Σ(k = 1 to n) 1/T(k).
    pub(super) fn inner_sums(&self, given: &membership::Facts) -> Vec<Node> {
        let Some((_, term)) = self.pointwise() else {
            return Vec::new();
        };
        term.walk()
            .into_iter()
            .filter(|part| {
                crate::methods::membership::Summed::of(part).is_some_and(|s| {
                    membership::divides_by(
                        s.body,
                        s.index,
                        index_system(s.start),
                        given,
                    )
                })
            })
            .collect()
    }

    /// Whether `node` says an inner sum's term at every point of its range
    /// (`inner_sums`), in the type's codomain.
    pub(super) fn says_inner_term(
        &self,
        node: &Node,
        given: &membership::Facts,
        ctx: &Context,
    ) -> bool {
        let Some(codomain) = self.asked.children.get(2) else {
            return false;
        };
        let Some(system) = System::of_sign(&codomain.text) else {
            return false;
        };
        self.inner_sums(given).iter().any(|sum| {
            crate::methods::membership::Summed::of(sum)
                .is_some_and(|s| membership::said_pointwise(node, &s, system, ctx))
        })
    }

    /// Whether `node` says, at every point of a set holding the type's
    /// domain, that the term is in the type's codomain: `for all k ∈ ℕ,
    /// 1/T(k) ∈ ℝ` for `t : {1, …, n} → ℝ`, ℕ holding every member of a
    /// range from 1.
    pub(super) fn said_pointwise(
        &self,
        node: &Node,
        known: &Known,
        ctx: &Context,
    ) -> bool {
        let (Some((letter, term)), [_, domain, codomain]) =
            (self.pointwise(), self.asked.children.as_slice())
        else {
            return false;
        };
        let [bound, set, body] = node.children.as_slice() else {
            return false;
        };
        if node.notation() != FOR_ALL || body.notation() != MEMBERSHIP {
            return false;
        }
        let [value, into] = body.children.as_slice() else {
            return false;
        };
        let at = Binding::from([(Symbol::of(letter), bound.clone())]);
        let holds = known.alike(set, domain)
            || (set.notation() == NUMBER_SYSTEMS
                && range_system(domain).is_some_and(|inside| {
                    System::of_sign(&set.text).is_some_and(|s| inside.within(s))
                }));
        let lands = known.alike(into, codomain)
            || (into.notation() == NUMBER_SYSTEMS
                && codomain.notation() == NUMBER_SYSTEMS
                && System::maybe_within(
                    System::of_sign(&into.text),
                    System::of_sign(&codomain.text),
                ));
        holds && lands && known.alike(&substitute_apart(term, &at, ctx), value)
    }

    /// Whether `node` states this type, an open letter standing for any set.
    pub(super) fn stated_by(&self, node: &Node, known: &Known) -> bool {
        let (asked, said) = (&self.asked, node);
        asked.notation() == said.notation()
            && asked.children.len() == said.children.len()
            && asked.children.iter().zip(&said.children).all(|(a, s)| {
                (a.is_name() && self.open.contains(a.text.as_str()))
                    || known.alike(a, s)
            })
    }
}

pub(super) fn family_asks(step: &Step, known: &Known, library: &Library) -> FamilyAsks {
    let just = &step.just;
    let groups = just
        .cited_item()
        .and_then(|item| library.groups(&just.item(&item)))
        .expect("a step whose item was just read");
    let parts = known.read_out_parts(step, library);
    let mut held = BTreeSet::new();
    let mut values = Vec::new();
    // The item's function types under what the citation writes for its
    // letters, `f := F`, where that makes the function one no `let` types:
    // one the proof defines, its rule, where the step cites the define and
    // the rule is written out, or its name, where it does not; or one a let
    // says only is a function on a set. A type a let declares is not asked
    // for (`GRAMMAR.md`, the function's type is a declaration). What the
    // step claims is no guide to the letters: an `obtain` claims the
    // witness, not the item's conclusion.
    let in_scope = typed_in_scope(known, step);
    let declared: BTreeSet<Symbol> =
        in_scope.iter().map(|t| t.children[0].text).collect();
    // What the citation writes, and what the match of the item against the
    // claim and the cited lines fixes beside it: `g is continuous on D`
    // claimed by `def:continuous-on` makes the item's f the page's g
    // whether or not the step writes f := g.
    let mut fixed = parts.seed.clone();
    // What the match makes a function the item applies, a rule: a sum's
    // summand, which a type asks of every point (`AskedType::pointwise`).
    let mut rules = Binding::new();
    // An obtain claims the witness, and is read for what it obtains through.
    let read = searched(step, search_of(step), known, library);
    if let Some(Built(taken)) = read.as_deref() {
        for (name, value) in &taken.binding {
            if value.notation() == PROPERTY_OF {
                rules.insert(*name, value.clone());
            } else if !fixed.contains_key(name) {
                fixed.insert(*name, value.clone());
            }
        }
    }
    let in_scope = typed_in_scope(known, step);
    let types = library
        .function_types(&just.item(&just.cited_item().expect("a cited item")))
        .iter()
        .map(|t| {
            let asked = substitute_apart(t, &fixed, &library.ctx);
            let rule = rules
                .get(t.children[0].text.as_str())
                .cloned()
                .or_else(|| on_a_part(&asked, &in_scope, known));
            AskedType {
                asked,
                open: t.children[1..]
                    .iter()
                    .filter(|s| s.is_name() && !fixed.contains_key(&s.text))
                    .map(|s| s.text.to_string())
                    .collect(),
                filled: fixed.contains_key(&t.children[0].text),
                rule,
            }
        })
        .collect::<Vec<AskedType>>();
    // A letter the citation leaves unfilled is the item's own, whatever the
    // page calls by the same name: sum-termwise's u, read as a rule, is no
    // page's `let u : ℕ → ℝ`. One the citation fills with a function a let
    // declares is kept apart: its type is not asked for, its codomain is
    // (`GRAMMAR.md`). Its type is asked where the item asks it over a set
    // its declared domain does not hold: product-single at a := 1 asks
    // a : {1, …, 1} → ℝ of a function declared on {1, …, n}, and the kernel
    // asks each a(k) to be a number where the page has not said that k is
    // in a's domain.
    let (types, declared_types): (Vec<AskedType>, Vec<AskedType>) =
        types.into_iter().partition(|t| {
            let function = &t.asked.children[0];
            t.rule.is_some()
                || function.notation() == PROPERTY_OF
                || (function.is_name()
                    && (!t.filled
                        || !declared.contains(&function.text)
                        || !declared_domain_holds(t, &in_scope, known)))
        });
    let declared_types = declared_types
        .into_iter()
        .filter(|t| t.asked.children[0].is_name())
        .collect();
    for group in groups.iter() {
        let gives = &group.gives;
        let mut trees = gives.clone();
        trees.extend(group.asked().cloned());
        let mut sites = Sites::new();
        for t in &trees {
            binding_sites(t, &library.ctx, &[], &mut sites);
        }
        let variables = group.letters(&trees);
        // What a function letter stands for is read where the item applies
        // it: its conclusions against what the step claims, and its
        // hypotheses against what the step cites, since an `obtain` claims
        // the witness and says nothing of the function.
        let mut pairs: Vec<(Node, &Node)> = Vec::new();
        for concl in gives {
            for reading in readings(concl, library) {
                for cand in conjuncts(&reading.claimed, library) {
                    for claim in &parts.claims {
                        pairs.push((cand.clone(), claim));
                    }
                }
            }
        }
        for hyp in group.asked() {
            for fact in &parts.facts {
                pairs.push((hyp.clone(), fact));
            }
        }
        for (pattern, ground) in &pairs {
            let found = match_tree(
                pattern,
                ground,
                &parts.seed,
                &variables,
                &sites,
                &library.ctx,
            );
            for value in found.iter().flat_map(|b| b.values()) {
                if value.notation() == PROPERTY_OF {
                    for n in value.children[0].names() {
                        if n != value.text {
                            held.insert(n);
                        }
                    }
                    values.push(value.clone());
                }
            }
        }
    }
    FamilyAsks {
        held,
        values,
        types,
        declared_types,
        letters: super::super::library::introduced(known, step),
        in_scope,
        ctx: library.ctx.clone(),
    }
}

impl FamilyAsks {
    /// What the one membership rule reads over no lines at the step
    /// (`membership::shown`): its letters and the function types in scope.
    pub(super) fn unlined<'a>(&'a self, known: &'a Known) -> membership::Facts<'a> {
        membership::Facts {
            facts: &[],
            letters: self.letters.clone(),
            ranged: IndexMap::new(),
            typed: &self.in_scope,
            in_sums: &self.in_scope,
            targets: known.targets,
            ctx: &self.ctx,
        }
    }

    /// Whether `node`, a line the citation names, states what a function
    /// hypothesis asks: its type, or a sum's term at every point.
    pub(super) fn states(&self, node: &Node, known: &Known) -> bool {
        self.types.iter().any(|t| {
            t.stated_by(node, known)
                || t.said_pointwise(node, known, &self.ctx)
                || t.says_inner_term(node, &self.unlined(known), &self.ctx)
        })
    }

    /// Whether `node`, a line the citation names, says the values a function
    /// hypothesis asks of one of the page's functions over the set the item
    /// asks it on, `for all k ∈ {1, …, j}, a(k) ∈ ℝ` for `a : {1, …, j} → ℝ`
    /// (`values_said`).
    pub(super) fn states_values(&self, node: &Node, library: &Library) -> bool {
        self.types
            .iter()
            .any(|t| t.filled && values_said(&t.asked, slice::from_ref(node), library))
    }

    /// Whether one requires line's fact is a membership the item's function
    /// hypotheses ask for, read as the checks of its step read it.
    pub(super) fn asks(&self, step: &Step, fact: &Written, known: &Known) -> bool {
        let Some(node) = known.whole(step, fact) else {
            return false;
        };
        if node.notation() == FUNCTION_TYPE {
            return self.types.iter().any(|t| t.stated_by(&node, known));
        }
        if self
            .types
            .iter()
            .any(|t| t.said_pointwise(&node, known, &self.ctx))
        {
            return true;
        }
        // Or the hypothesis said whole, of every value the function takes:
        // `x : ℕ → ℝ` where x(n) is a partial sum of the reciprocals of T
        // asks that every partial sum be real. T is a defined function and
        // no name a membership could be asked of, so what is compared is the
        // value itself, read at the name the line binds.
        if node.notation() == FOR_ALL && node.children.len() == 3 {
            let (bound, body) = (&node.children[0], &node.children[2]);
            if body.notation() != MEMBERSHIP
                || body.children[1].notation() != NUMBER_SYSTEMS
            {
                return false;
            }
            // A function the proof defines, whose type the item asks over a
            // set the define may not name: the type said of every point,
            // `for all i ∈ {1, …, k + 1}, t(i) ∈ ℝ`, which holds where
            // `t : {1, …, k + 1} → ℝ` does not, t's domain being the
            // define's.
            let (set, value) = (&node.children[1], &body.children[0]);
            let pointwise = value.notation() == APPLICATION
                && value.children.len() == 2
                && known.alike(&value.children[1], bound)
                && self.types.iter().any(|t| {
                    let [f, d, e] = t.asked.children.as_slice() else {
                        return false;
                    };
                    f.is_name()
                        && known.alike(f, &value.children[0])
                        && ((d.is_name() && t.open.contains(d.text.as_str()))
                            || known.alike(d, set))
                        && known.alike(e, &body.children[1])
                });
            if pointwise {
                return true;
            }
            // The line's letter is put into the value apart from what the
            // value binds, and the two compared up to their bound letters:
            // `Σ(n = 1 to k) 1/T(n)` at k is `Σ(a = 1 to k) 1/T(a)`.
            let none = IndexMap::new();
            return self.values.iter().any(|v| {
                let mut at = Binding::new();
                at.insert(v.text, bound.clone());
                let value = substitute_apart(&v.children[0], &at, &self.ctx);
                alike(&value, &body.children[0], &self.ctx, &none, &none)
            });
        }
        node.notation() == MEMBERSHIP
            && node.children[1].notation() == NUMBER_SYSTEMS
            && !node.children[0].names().is_empty()
            && node.children[0].names().is_subset(&self.held)
    }
}

/// What the functions a proof defines ask of what the step's claim applies
/// them to: `define M(X) := …, for X ∈ 𝒫A` and a claim holding M(X) ask
/// `X ∈ 𝒫A`, since M(X) is M's rule only there. The checker reads the name
/// as its rule without asking, and the kernel does not (`SYNTAX.md`: a
/// define may name a function). A line the step cites that applies one is
/// read as its rule too where the step cites the define, as `S ∈ G(m − 1,
/// n)` is unfolded by citing G's define, and asks the same of what it is
/// applied to.
pub(in crate::checker) fn domains_asked(
    thm: &Theorem,
    step: &Step,
    scopes: &[FileScope],
    known: &Known,
) -> FxIndexSet<ByShape> {
    let functions = defined_functions(&proof::in_scope(thm, scopes));
    let Some(claim) = known.whole_as_written(&step.claim) else {
        return FxIndexSet::default(); // `check_formulas` says it does not read
    };
    let cited: Vec<Defined> = functions
        .iter()
        .filter(|d| d.label.as_ref().is_some_and(|l| step.just.refs.contains(l)))
        .cloned()
        .collect();
    applied(&functions, &claim, false, known)
        .into_iter()
        .chain(applied_in_cited(step, &cited, known, known.ctx))
        .chain(read_over_cited_theorem(thm, step, scopes, known))
        .flat_map(|a| a.says)
        .map(ByShape)
        .collect()
}
