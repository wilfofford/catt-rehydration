use thiserror::Error;
use std::fmt::Debug;
use std::ops::Range;

use crate::common::{CtxT, Tree, Path, Eval, Environment};
use crate::normal::{TermN, TypeN};
use crate::term::{ArgsWithTypeT, TermT, TypeT};
use crate::eval::SemCtx;
use crate::typecheck::{TypeCheckError, Local};


#[derive(Error, Debug)]
pub enum CoverError<S>
where
{
    #[error(transparent)]
    AuxConcatError(#[from] ConcatError),
    #[error("Cannot wedge empty tree")]
    EmptyConcatError, 
    #[error(transparent)]
    TypeCheckError(#[from] TypeCheckError<S>),
}


#[derive(Error, Debug)]
pub enum ConcatError
where {
    #[error("Cannot wedge trees with mismatched boundary")]
    ConcatError
}


pub struct Cover<T : Clone> {
    pub(crate) length : usize,
    pub(crate) term : TermT<Path>,
    pub(crate) ctx : SemCtx<Path,Path>,
    pub(crate) sub : ArgsWithTypeT<Path, T>
}


impl<T : Clone> Tree<T> {
    pub(crate) fn get_dim_one(&self) -> Vec<T> {
        let mut concatenated_elements: Vec<T> = Vec::new();
        for branch in self.branches.clone() {

            concatenated_elements.extend(branch.elements);
        }
        concatenated_elements
    }
}


impl<T: Clone + PartialEq> Tree<T> {
    pub fn wedge(&self, other: &Tree<T>) -> Tree<T> {
        let mut new_elements = self.elements.clone();
        let mut new_branches = self.branches.clone();
        let _ = new_elements.pop();
        new_elements.extend_from_slice(&other.elements);
        new_branches.extend_from_slice(&other.branches);
        Tree {
            elements: new_elements,
            branches: new_branches,
        }
    }
}

// impl<S: Clone + Debug> TermE<S> {
//     pub(crate) fn uc<T: Eval>(&self, 
//         env: &Environment,
//         local: &Local<T>,) -> Result<Cover<T>,CoverError<S>> {
//             let (tmt, tyt) = self.check(env, local)?;
//             let sem_ctx = local.ctx.id_sem_ctx();
//             let tmn = tmt.eval(&sem_ctx, env);
//             let tyn = tyt.eval(&sem_ctx, env);
//             match tmn {
//                 TermN::Variable(_) => {
//                     let length = 1;
//                     let term = TermT::Var(Path{here:0, path:vec![0]});
//                     let ctx = SemCtx::new(Tree{
//                         elements : vec![TermN::Variable(Path{here:0, path:vec![]}),
//                                         TermN::Variable(Path{here:1,path:vec![]})],
//                         branches : vec![Tree::singleton(TermN::Variable(Path{here:0,path:vec![0]}))]
//                     },TypeN(vec![]));
//                     let TypeT::Arr(src, _, tgt) = tyn.quote();
//                     let sub = ArgsWithTypeT {
//                         args : Tree{
//                             elements: vec![src,tgt],
//                             branches: vec![Tree::singleton(tmt)]
//                         },
//                         ty : Box::new(TypeT::Base)
//                     };
//                     Ok(Cover{length, term, ctx, sub})

//                 }
//                 TermN::Other(h, tr) => {
//                     let length = tr.get_dim_one()
//                     .iter()
//                     .map(|t| t.uc_length())
//                     .sum();
//                     if length == 0 {
//                         let idargs = Tree::singleton(TermT::Var(Path{here:0,path:vec![]}));
//                         let term = TermT::AppPath(Box::new(TermT::Id(0)),ArgsWithTypeT{args:idargs, ty:Box::new(TypeT::Base)});
//                         let ctx = SemCtx::new(Tree::singleton(TermN::Variable(Path{here:0,path:vec![]})), TypeN(vec![]));
//                         let TypeT::Arr(src, _, tgt) = tyn.quote();
//                         let sub = ArgsWithTypeT {
//                             args : Tree{
//                                 elements: vec![src],
//                                 branches: vec![Tree{elements:vec![], branches:vec![]}]
//                             },
//                             ty : Box::new(TypeT::Base)
//                         };
//                         Ok(Cover{length, term, ctx, sub})
//                     } else {
//                         let mut startpoints = vec![0];
//                         let mut current_length = 0;
//                         for &t in tr.get_dim_one().iter() {
//                             current_length += t.uc_length();
//                             startpoints.push(current_length);
//                         };
//                         let n = startpoints.len();
//                         let mut args = Tree{
//                             elements : vec![TermT::Var(Path{here:0, path:vec![]})],
//                             branches : vec![]
//                         };
//                         let TypeT::Arr(src, _, tgt) = tyn.quote();
//                         let mut subargs = Tree::singleton(src);
//                         for i in 0..(n-1) {
//                                 args.elements.push(TermT::Var(Path{here:startpoints[i+1], path:vec![]}));                    
//                                 let subcover = tr.branches[i].elements[0].uc_term(); 
//                                 let arg = TermT::AppPath(Box::new(subcover), 
//                                     injection(startpoints[i],startpoints[i+1]));
//                                     args.branches.push(Tree {elements: vec![arg], branches: vec![]});    
//                                 subargs = subargs.wedge(&tr.branches[i].elements[0].quote().to_expr(Some(&local.ctx),env.implicits).uc(env,local)?.sub.args);
//                         };
//                         let term = TermT::AppPath(Box::new(h.quote()), ArgsWithTypeT{args:args, ty:Box::new(TypeT::Base)});

//                         let mut elements = vec![];
//                         let mut branches = vec![];
//                         for i in 0..(n+1) {
//                             elements.push(TermN::Variable(Path{here: i , path : vec![]}));
//                             if i != n {
//                                 branches.push(Tree {elements: vec![TermN::Variable(Path{here:0, path: vec![i]})], branches: vec![]});
//                             }
//                         };
//                         let ctx = SemCtx::new(Tree{ elements, branches }, TypeN(vec![]));
//                         let sub = ArgsWithTypeT{args:subargs, ty:Box::new(TypeT::Base)};
//                         Ok(Cover{length, term, ctx, sub})
//                     }
                    
//                 }
//             }
//         }
// }


impl<T:Eval + Clone> TermT<T> {
    pub(crate) fn uc(&self, 
        env: &Environment,
        local: &Local<T>,) -> Result<Cover<T>,CoverError<Range<usize>>> {
            let sem_ctx = local.ctx.id_sem_ctx();
            let tmn = self.eval(&sem_ctx, env);
            match tmn {
                TermN::Variable(p) => {
                    let length = 1;
                    let term = TermT::Var(Path{here:0, path:vec![0]});
                    let ctx = SemCtx::new(Tree{
                        elements : vec![TermN::Variable(Path{here:0, path:vec![]}),
                                        TermN::Variable(Path{here:1,path:vec![]})],
                        branches : vec![Tree::singleton(TermN::Variable(Path{here:0,path:vec![0]}))]
                    },TypeN(vec![]));
                    let tyt = p.type_in(&local.ctx);
                    let tyn = tyt.eval(&sem_ctx, env);
                    let (src,tgt) = match tyn.quote() {
                        TypeT::Arr(s, _, t) => (s,t),
                        _ => unreachable!()
                    };
                    let sub = ArgsWithTypeT {
                        args : Tree{
                            elements: vec![src,tgt],
                            branches: vec![Tree::singleton(self.clone())]
                        },
                        ty : Box::new(TypeT::Base)
                    };
                    Ok(Cover{length, term, ctx, sub})

                }
                TermN::Other(h, tr) => {
                    let length = tr.get_dim_one()
                    .iter()
                    .map(|t| t.uc_length())
                    .sum();
                    if length == 0 {
                        let idargs = Tree::singleton(TermT::Var(Path{here:0,path:vec![]}));
                        let term = TermT::AppPath(Box::new(TermT::Id(0)),ArgsWithTypeT{args:idargs, ty:Box::new(TypeT::Base)});
                        let ctx = SemCtx::new(Tree::singleton(TermN::Variable(Path{here:0,path:vec![]})), TypeN(vec![]));
                        let src = tr.elements[0].quote();
                        let sub = ArgsWithTypeT {
                            args : Tree{
                                elements: vec![src],
                                branches: vec![Tree{elements:vec![], branches:vec![]}]
                            },
                            ty : Box::new(TypeT::Base)
                        };
                        Ok(Cover{length, term, ctx, sub})
                    } else {
                        let mut startpoints = vec![0];
                        let mut current_length = 0;
                        for t in tr.get_dim_one().iter() {
                            current_length += t.uc_length();
                            startpoints.push(current_length);
                        };
                        let n = startpoints.len();
                        let mut args = Tree{
                            elements : vec![TermT::Var(Path{here:0, path:vec![]})],
                            branches : vec![]
                        };
                        let src = tr.elements[0].quote();
                        let mut subargs = Tree::singleton(src);
                        for i in 0..(n-1) {
                                args.elements.push(TermT::Var(Path{here:startpoints[i+1], path:vec![]}));                    
                                let subcover = tr.branches[i].elements[0].uc_term(); 
                                let arg = TermT::AppPath(Box::new(subcover), 
                                    injection(startpoints[i],startpoints[i+1]));
                                    args.branches.push(Tree {elements: vec![arg], branches: vec![]});    
                                subargs = subargs.wedge(&tr.branches[i].elements[0].quote().uc(env,local)?.sub.args);
                        };
                        let term = TermT::AppPath(Box::new(h.quote()), ArgsWithTypeT{args:args, ty:Box::new(TypeT::Base)});

                        let mut elements = vec![];
                        let mut branches = vec![];
                        for i in 0..(n+1) {
                            elements.push(TermN::Variable(Path{here: i , path : vec![]}));
                            if i != n {
                                branches.push(Tree {elements: vec![TermN::Variable(Path{here:0, path: vec![i]})], branches: vec![]});
                            }
                        };
                        let ctx = SemCtx::new(Tree{ elements, branches }, TypeN(vec![]));
                        let sub = ArgsWithTypeT{args:subargs, ty:Box::new(TypeT::Base)};
                        Ok(Cover{length, term, ctx, sub})
                    }
                    
                }
            }
        }
}



impl<T : Clone> TermN<T> {

    pub(crate) fn uc_length(&self) -> usize {
        match self {
            TermN::Variable(_) => 1,
            TermN::Other(_, tr) => {tr.get_dim_one()
                                                    .iter()
                                                    .map(|t| t.uc_length())
                                                    .sum()}
        }
    }

    pub(crate) fn uc_term(&self) -> TermT<Path> {
        match self {
            TermN::Variable(_) => TermT::Var(Path{here:0, path:vec![0]}),
            TermN::Other(h, tr) => {
                let mut startpoints = vec![0];
                let mut current_length = 0;
                for t in tr.get_dim_one().iter() {
                    current_length += t.uc_length();
                    startpoints.push(current_length);
                };
                let n = startpoints.len();
                let idargs = Tree::singleton(TermT::Var(Path{here:0,path:vec![]}));
                let idp0 = TermT::AppPath(Box::new(TermT::Id(0)),ArgsWithTypeT{args:idargs, ty:Box::new(TypeT::Base)});
                if n == 1 {
                    idp0
                } else {
                let mut args = Tree{
                    elements : vec![TermT::Var(Path{here:0, path:vec![]})],
                    branches : vec![]
                };
                for i in 0..(n-1) {
                        args.elements.push(TermT::Var(Path{here:startpoints[i+1], path:vec![]}));                    
                        let subcover = tr.branches[i].elements[0].uc_term(); 
                        let arg = TermT::AppPath(Box::new(subcover), 
                            injection(startpoints[i],startpoints[i+1]));
                            args.branches.push(Tree {elements: vec![arg], branches: vec![]});    
                };
                TermT::AppPath(Box::new(h.quote()), ArgsWithTypeT{args:args, ty:Box::new(TypeT::Base)})
                }
            }
        }
    }

    pub(crate) fn uc_ctx(&self) -> SemCtx<Path,Path> {
        let n = self.uc_length();
        let mut elements = vec![];
        let mut branches = vec![];
        for i in 0..(n+1) {
            elements.push(TermN::Variable(Path{here: i , path : vec![]}));
            if i != n {
                branches.push(Tree {elements: vec![TermN::Variable(Path{here:0, path: vec![i]})], branches: vec![]});
            }
        };
        SemCtx::new(Tree{ elements, branches }, TypeN(vec![]))
    }
}

pub(crate) fn injection(i : usize, j : usize) -> ArgsWithTypeT<Path, Path> {
    let mut tree = Tree{
        elements: Vec::new(),
        branches: Vec::new()
    };
    for n in i..(j+1) {
        tree.elements.push(TermT::Var(Path{here: n, path: Vec::new()}));
    };
    for n in i..j {
        tree.branches.push(Tree::singleton(TermT::Var(Path{here:0, path:vec![n]})));
    };
    ArgsWithTypeT{args:tree, ty:Box::new(TypeT::Base)}
}