use crate::common::{Tree, Path};
use crate::normal::{TermN, TypeN};
use crate::term::{ArgsWithTypeT, TermT, TypeT};
use crate::eval::SemCtx;


impl<T> Tree<T> {
    pub(crate) fn get_dim_one(&self) -> Vec<&T> {
        let mut concatenated_elements: Vec<&T> = Vec::new();
        for branch in &self.branches {

            concatenated_elements.extend(branch.elements.iter());
        }
        concatenated_elements
    }
}

impl<T> TermN<T> {
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
                if n == 1 {
                    TermT::IdT(1)
                } else {
                let mut args = Tree{
                    elements : vec![],
                    branches : vec![]
                };
                for i in 0..n {
                    args.elements.push(TermT::Var(Path{here:i, path:vec![]}));
                    if i != (n-1) {
                        let subcover = tr.branches[i].elements[0].uc_term();
                        if subcover == TermT::IdT(1) {
                            let arg = subcover;
                            args.branches.push(Tree {elements: vec![arg], branches: vec![]});
                        } else {
                            let arg = TermT::AppPath(Box::new(subcover), 
                                injection(startpoints[i],startpoints[i+1]));
                            args.branches.push(Tree {elements: vec![arg], branches: vec![]});
                        }  
                    };
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
        SemCtx{map:Tree{ elements, branches }, ty: TypeN(vec![])}
    }
}

pub(crate) fn injection(i : usize, j : usize) -> ArgsWithTypeT<Path, Path> {
    let mut tree = Tree{
        elements: Vec::new(),
        branches: Vec::new()
    };
    for n in i..j {
        tree.elements.push(TermT::Var(Path{here: n, path: Vec::new()}));
    };
    for n in i..(j-1) {
        tree.branches.push(Tree::singleton(TermT::Var(Path{here:0, path:vec![n]})));
    };
    ArgsWithTypeT{args:tree, ty:Box::new(TypeT::Base)}
}