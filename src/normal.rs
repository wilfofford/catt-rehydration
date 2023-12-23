use std::{collections::HashSet, ops::Deref};

use derivative::Derivative;
use ref_cast::RefCast;

use crate::{
    common::{Name, NoDispOption, Path, Pos, Tree},
    typecheck::Support,
};

#[derive(Clone, Debug, Eq, Derivative)]
#[derivative(PartialEq)]
pub enum HeadN {
    CohN {
        tree: Tree<NoDispOption<Name>>,
        ty: TypeN,
    },
    UCohN {
        tree: Tree<NoDispOption<Name>>,
    },
    IdN {
        dim: usize,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TermN {
    Variable(Pos),
    Other(HeadN, Tree<TermN>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeN(pub Vec<(TermN, TermN)>);

#[derive(Debug, PartialEq, Eq, RefCast)]
#[repr(transparent)]
pub struct TypeNRef(pub [(TermN, TermN)]);

impl Deref for TypeN {
    type Target = TypeNRef;

    fn deref(&self) -> &Self::Target {
        TypeNRef::ref_cast(&self.0)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CtxN {
    Ctx(Vec<TypeN>),
    Tree(Tree<NoDispOption<Name>>),
}

impl HeadN {
    pub fn susp(self) -> HeadN {
        match self {
            HeadN::CohN { tree, ty } => HeadN::CohN {
                tree: tree.susp(),
                ty: ty.susp(),
            },
            HeadN::UCohN { tree } => HeadN::UCohN { tree: tree.susp() },
            HeadN::IdN { dim } => HeadN::IdN { dim: dim + 1 },
        }
    }
}

impl TermN {
    pub fn susp(self) -> TermN {
        match self {
            TermN::Variable(p) => TermN::Variable(p.susp()),
            TermN::Other(head, args) => TermN::Other(head.susp(), args.susp_args()),
        }
    }

    pub fn to_args(self, ty: TypeN) -> Tree<TermN> {
        ty.0.into_iter()
            .rfold(Tree::singleton(self), |tr, (s, t)| Tree {
                elements: vec![s, t],
                branches: vec![tr],
            })
    }

    pub fn free_vars(&self, set: &mut HashSet<Path>) {
        match self {
            TermN::Variable(Pos::Path(p)) => {
                set.insert(p.clone());
            }
            TermN::Variable(_) => {}
            TermN::Other(_, args) => {
                for (_, tm) in args.get_paths() {
                    tm.free_vars(set);
                }
            }
        }
    }
}

impl TypeN {
    pub fn base() -> TypeN {
        TypeN(vec![])
    }

    pub fn dim(&self) -> usize {
        self.0.len()
    }

    pub fn susp(self) -> TypeN {
        let mut base = vec![(
            TermN::Variable(Pos::Path(Path::here(0))),
            TermN::Variable(Pos::Path(Path::here(1))),
        )];
        base.extend(self.0.into_iter().map(|(s, t)| (s.susp(), t.susp())));
        TypeN(base)
    }

    pub fn free_vars(self) -> HashSet<Path> {
        let mut set = HashSet::new();
        for (s, t) in self.0 {
            s.free_vars(&mut set);
            t.free_vars(&mut set);
        }
        set
    }

    pub fn support_check<T>(mut self, tree: &Tree<T>, support: &Support) -> bool {
        match support {
            Support::FullInverse => {
                if let Some((s, t)) = self.0.pop() {
                    let mut src = self.free_vars();
                    let dim = tree.dim();
                    if dim >= 1 {
                        let path_tree = tree.path_tree();
                        let mut tgt = src.clone();
                        s.free_vars(&mut src);
                        t.free_vars(&mut tgt);

                        if (path_tree
                            .bdry_set(dim - 1, true)
                            .into_iter()
                            .cloned()
                            .collect::<HashSet<_>>()
                            == src)
                            && (path_tree
                                .bdry_set(dim - 1, false)
                                .into_iter()
                                .cloned()
                                .collect::<HashSet<_>>()
                                == tgt)
                        {
                            return true;
                        }
                    } else {
                        s.free_vars(&mut src);
                    }
                    t.free_vars(&mut src);

                    tree.get_paths().into_iter().all(|(p, _)| src.contains(&p))
                } else {
                    false
                }
            }
            Support::NoInverse => true,
        }
    }

    pub(crate) fn is_unbiased<T>(&self, tree: &Tree<T>) -> bool {
        if let Some((s, t)) = self.0.last() {
            let path_tree = tree.path_tree().map(&|p| TermN::Variable(Pos::Path(p)));
            let dim = tree.dim();
            let src = path_tree.bdry(dim - 1, false);
            let src_correct = if let Some(x) = src.get_max() {
                s == x
            } else if let TermN::Other(HeadN::UCohN { .. }, args) = s {
                args == &src
            } else {
                false
            };
            if !src_correct {
                return false;
            }
            let tgt = path_tree.bdry(dim - 1, true);
            let tgt_correct = if let Some(x) = tgt.get_max() {
                s == x
            } else if let TermN::Other(HeadN::UCohN { .. }, args) = t {
                args == &tgt
            } else {
                false
            };
            tgt_correct
        } else {
            true
        }
    }
}

impl Tree<NoDispOption<Name>> {
    pub fn unbiased_type(&self, d: usize) -> TypeN {
        let ptree = self.path_tree().map(&|p| TermN::Variable(Pos::Path(p)));
        let inner = (0..d)
            .map(|x| {
                let src_args = ptree.bdry(x, false);
                let tgt_args = ptree.bdry(x, true);
                if src_args.is_disc() {
                    (src_args.unwrap_disc(), tgt_args.unwrap_disc())
                } else {
                    (
                        TermN::Other(
                            HeadN::UCohN {
                                tree: self.bdry(x, false),
                            },
                            src_args,
                        ),
                        TermN::Other(
                            HeadN::UCohN {
                                tree: self.bdry(x, true),
                            },
                            tgt_args,
                        ),
                    )
                }
            })
            .collect();

        TypeN(inner)
    }
}

impl Tree<TermN> {
    fn susp_args(self) -> Self {
        Tree {
            elements: vec![
                TermN::Variable(Pos::Path(Path::here(0))),
                TermN::Variable(Pos::Path(Path::here(1))),
            ],
            branches: vec![self.map(&|tm| tm.susp())],
        }
    }
}

impl TypeNRef {
    pub fn inner(&self) -> &Self {
        TypeNRef::ref_cast(&self.0[0..self.0.len() - 1])
    }
}
