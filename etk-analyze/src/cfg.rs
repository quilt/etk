use crate::blocks::annotated::ExitExt;

use etk_dasm::blocks::annotated::{AnnotatedBlock, Exit};

use petgraph::dot::Dot;
use petgraph::graph::{Graph, NodeIndex};

use std::collections::BTreeMap;
use std::convert::TryInto;
use std::fmt;

use z3::ast::{Ast, BV};
use z3::SatResult;

#[derive(Debug, Clone)]
enum Node {
    Terminate,
    BadJump,
    Block(Box<AnnotatedBlock>),
}

impl fmt::Display for Node {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let block = match self {
            Self::Terminate => return write!(f, "<terminate>"),
            Self::BadJump => return write!(f, "<bad-jump>"),
            Self::Block(b) => b,
        };

        write!(f, "Offset: 0x{:x}", block.offset)
    }
}

struct Edge;

impl fmt::Display for Edge {
    fn fmt(&self, _: &mut fmt::Formatter) -> fmt::Result {
        Ok(())
    }
}

impl Node {
    fn unwrap_block(&self) -> &AnnotatedBlock {
        match self {
            Self::Block(b) => b,
            _ => panic!("not a block"),
        }
    }
}

pub struct ControlFlowGraph {
    by_offset: BTreeMap<usize, NodeIndex>,
    graph: Graph<Node, Edge>,
}

impl fmt::Debug for ControlFlowGraph {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        #[derive(Debug)]
        struct ControlFlowGraph<'a> {
            #[allow(dead_code)]
            by_offset: &'a BTreeMap<usize, NodeIndex>,
            #[allow(dead_code)]
            node_count: usize,
            #[allow(dead_code)]
            edge_count: usize,
        }

        let helper = ControlFlowGraph {
            by_offset: &self.by_offset,
            node_count: self.graph.node_count(),
            edge_count: self.graph.edge_count(),
        };

        helper.fmt(f)
    }
}

impl ControlFlowGraph {
    pub fn new<I>(blocks: I) -> Self
    where
        I: Iterator<Item = AnnotatedBlock>,
    {
        let mut graph = Graph::<Node, Edge>::new();
        let mut by_offset = BTreeMap::new();
        let mut jump_targets = Vec::new();

        let terminate = graph.add_node(Node::Terminate);
        let bad_jump = graph.add_node(Node::BadJump);

        for block in blocks {
            let is_jump_target = block.jump_target;
            let offset = block.offset;
            let idx = graph.add_node(Node::Block(Box::new(block)));
            let replaced = by_offset.insert(offset, idx);
            assert_eq!(replaced, None);

            if is_jump_target {
                jump_targets.push(idx);
            }
        }

        for idx in by_offset.values() {
            let idx = *idx;
            let node = &graph[idx];

            let block = match node {
                Node::Block(b) => b,
                _ => continue,
            };

            let exit = block.exit.erase();

            let mut fall_through_idx = None;

            // Add edge to fall-through (aka the next instruction after this block.)
            if let Some(fall_through) = block.exit.fall_through() {
                let next = by_offset.get(&fall_through);
                if let Some(next_idx) = next {
                    // If the fallthrough matches a block, add an edge to it.
                    graph.add_edge(idx, *next_idx, Edge);
                    fall_through_idx = Some(next_idx);
                } else {
                    // If the fallthough doesn't match a block, add an edge to
                    // <terminate>.
                    graph.add_edge(idx, terminate, Edge);
                }
            };

            match exit {
                Exit::Unconditional(_) => (),
                Exit::Branch { .. } => (),
                Exit::Terminate => {
                    // Terminate isn't a jump, so it can never be a bad one.
                    graph.add_edge(idx, terminate, Edge);
                    continue;
                }
                Exit::FallThrough(_) => {
                    // Fallthrough is never a jump, so it can never be a bad one.
                    continue;
                }
            }

            // Assume all jumps can be bad.
            graph.add_edge(idx, bad_jump, Edge);

            for jump_target in jump_targets.iter() {
                if Some(jump_target) == fall_through_idx {
                    // Edge was added earlier.
                    continue;
                }

                // Assume all jumps can go to any jump target.
                graph.add_edge(idx, *jump_target, Edge);
            }
        }

        Self { by_offset, graph }
    }

    fn shallow_block(&mut self, from: NodeIndex, to: NodeIndex) -> bool {
        let from = self.graph[from].unwrap_block();
        let to = self.graph[to].unwrap_block();

        let config = z3::Config::new();
        let context = z3::Context::new(&config);
        let target = BV::from_u64(&context, to.offset.try_into().unwrap(), 256);

        let ast = match from.exit.to_z3(&context) {
            Exit::Terminate => unreachable!(),
            Exit::FallThrough(f) => {
                return f == to.offset;
            }
            Exit::Unconditional(u) => u,
            Exit::Branch {
                when_true,
                when_false,
                condition,
            } => {
                let when_false: u64 = when_false.try_into().unwrap();
                let when_false = BV::from_u64(&context, when_false, 256);
                let zero = BV::from_u64(&context, 0, 256);
                condition._eq(&zero).ite(&when_false, &when_true)
            }
        };

        let solver = z3::Solver::new(&context);
        solver.assert(&ast._eq(&target));
        let result = solver.check();

        !matches!(result, SatResult::Unsat)
    }

    fn shallow_bad_jump(&mut self, from: NodeIndex) -> bool {
        let from = self.graph[from].unwrap_block();

        let config = z3::Config::new();
        let context = z3::Context::new(&config);
        let solver = z3::Solver::new(&context);

        let ast = match from.exit.to_z3(&context) {
            Exit::FallThrough(_) => return false,
            Exit::Terminate => unreachable!(),
            Exit::Unconditional(u) => u,
            Exit::Branch {
                when_true,
                condition,
                ..
            } => {
                let zero = BV::from_u64(&context, 0, 256);
                solver.assert(&zero._eq(&condition).not());
                when_true
            }
        };

        for (offset, to_idx) in self.by_offset.iter() {
            if !self.graph[*to_idx].unwrap_block().jump_target {
                continue;
            }

            let bv = BV::from_u64(&context, (*offset).try_into().unwrap(), 256);
            solver.assert(&bv._eq(&ast).not());
        }

        let result = solver.check();

        !matches!(result, SatResult::Unsat)
    }

    fn shallow_terminate(&mut self, from: NodeIndex) -> bool {
        let from = self.graph[from].unwrap_block();

        let config = z3::Config::new();
        let context = z3::Context::new(&config);
        let solver = z3::Solver::new(&context);

        let ast = match from.exit.to_z3(&context) {
            Exit::FallThrough(_) => return true,
            Exit::Terminate => return true,
            Exit::Unconditional(_) => unreachable!(),
            Exit::Branch { condition, .. } => {
                let zero = BV::from_u64(&context, 0, 256);
                zero._eq(&condition)
            }
        };

        solver.assert(&ast);
        let result = solver.check();

        !matches!(result, SatResult::Unsat)
    }

    // https://github.com/rust-lang/rust-clippy/issues/6420
    #[allow(clippy::needless_collect)]
    pub fn refine_shallow(&mut self) {
        let indexes: Vec<_> = self
            .by_offset
            .values()
            .filter_map(|idx| {
                let node = &self.graph[*idx];
                match node {
                    Node::Block(_) => Some(*idx),
                    _ => None,
                }
            })
            .collect();

        for idx in indexes.into_iter() {
            let neighbors_indexes: Vec<_> = self.graph.neighbors(idx).collect();

            for neighbor_idx in neighbors_indexes.into_iter() {
                let neighbor = &self.graph[neighbor_idx];

                let keep = match neighbor {
                    Node::Block(_) => self.shallow_block(idx, neighbor_idx),
                    Node::BadJump => self.shallow_bad_jump(idx),
                    Node::Terminate => self.shallow_terminate(idx),
                };

                if !keep {
                    let edge = self.graph.find_edge(idx, neighbor_idx).unwrap();
                    self.graph.remove_edge(edge);
                }
            }
        }
    }

    pub fn render(&self) -> impl '_ + fmt::Display {
        Dot::new(&self.graph)
    }
}

#[cfg(test)]
mod tests {
    use assert_matches::assert_matches;

    use etk_asm::disasm::Disassembler;
    use etk_asm::ingest::Ingest;

    use etk_dasm::blocks::basic::Separator;

    use super::*;

    #[derive(Debug, Copy, Clone)]
    enum N {
        Offset(usize),
        BadJump,
        Terminate,
    }

    impl From<usize> for N {
        fn from(offset: usize) -> Self {
            Self::Offset(offset)
        }
    }

    struct CfgTest<C, U> {
        source: &'static str,
        connected: C,
        unconnected: U,
    }

    impl<C, U, Ci, Ui> CfgTest<C, U>
    where
        C: IntoIterator<Item = Ci>,
        U: IntoIterator<Item = Ui>,
        Ci: std::borrow::Borrow<(usize, N)>,
        Ui: std::borrow::Borrow<(usize, N)>,
    {
        fn compile(&self) -> Disassembler {
            let mut output = Disassembler::new();
            Ingest::new(&mut output)
                .ingest("./test", self.source)
                .unwrap();
            output
        }

        fn find_nodes(cfg: &ControlFlowGraph, from_off: usize, to_n: N) -> (NodeIndex, NodeIndex) {
            let terminate_idx: NodeIndex = 0.into();
            let bad_jump_idx: NodeIndex = 1.into();
            assert_matches!(cfg.graph[terminate_idx], Node::Terminate);
            assert_matches!(cfg.graph[bad_jump_idx], Node::BadJump);

            let from_idx = cfg.by_offset[&from_off];
            let to_idx = match to_n {
                N::Offset(offset) => cfg.by_offset[&offset],
                N::BadJump => bad_jump_idx,
                N::Terminate => terminate_idx,
            };

            (from_idx, to_idx)
        }

        fn check(self) {
            let mut program = self.compile();
            let mut separator = Separator::new();

            separator.push_all(program.ops());

            let blocks = separator
                .take()
                .into_iter()
                .chain(separator.finish().into_iter())
                .map(|x| AnnotatedBlock::annotate(&x));

            let mut cfg = ControlFlowGraph::new(blocks);
            cfg.refine_shallow();

            let connected = self
                .connected
                .into_iter()
                .map(|x| x.borrow().clone())
                .map(|(f, t)| Self::find_nodes(&cfg, f, t))
                .map(|(f, t)| (f, t, true));

            let unconnected = self
                .unconnected
                .into_iter()
                .map(|x| x.borrow().clone())
                .map(|(f, t)| Self::find_nodes(&cfg, f, t))
                .map(|(f, t)| (f, t, false));

            for (from_idx, to_idx, connected) in connected.chain(unconnected) {
                let from = &cfg.graph[from_idx];
                let to = &cfg.graph[to_idx];

                let found = cfg.graph.find_edge(from_idx, to_idx).is_some();
                if connected && !found {
                    panic!(
                        "edge between {} and {} was expected, but not found",
                        from, to,
                    );
                } else if !connected && found {
                    panic!(
                        "edge between {} and {} was not expected, but was found",
                        from, to,
                    );
                }
            }
        }
    }

    #[test]
    fn empty() {
        let source = "";

        CfgTest {
            source,
            connected: &[],
            unconnected: &[],
        }
        .check();
    }

    #[test]
    fn just_stop() {
        let source = "stop";

        CfgTest {
            source,
            connected: &[(0, N::Terminate)],
            unconnected: &[],
        }
        .check();
    }

    #[test]
    fn just_pc() {
        let source = "pc";

        CfgTest {
            source,
            connected: &[(0, N::Terminate)],
            unconnected: &[],
        }
        .check();
    }

    #[test]
    fn just_bad_jump() {
        let source = r#"
            push1 0
            jump
        "#;

        CfgTest {
            source,
            connected: &[(0, N::BadJump)],
            unconnected: &[(0, N::Terminate), (0, N::Offset(0))],
        }
        .check();
    }

    #[test]
    fn infinite_loop() {
        let source = r#"
            jumpdest
            push1 0
            jump
        "#;

        CfgTest {
            source,
            connected: &[(0, N::Offset(0))],
            unconnected: &[(0, N::Terminate), (0, N::BadJump)],
        }
        .check();
    }

    #[test]
    fn infinite_loop_with_branch() {
        let source = r#"
            jumpdest
            push1 1
            push1 0
            jumpi
        "#;

        CfgTest {
            source,
            connected: &[(0, N::Offset(0))],
            unconnected: &[(0, N::Terminate), (0, N::BadJump)],
        }
        .check();
    }

    #[test]
    fn fallthrough_branch() {
        let source = r#"
            jumpdest
            push1 0
            push1 100
            jumpi
        "#;

        CfgTest {
            source,
            connected: &[(0, N::Terminate)],
            unconnected: &[(0, N::Offset(0)), (0, N::BadJump)],
        }
        .check();
    }

    #[test]
    fn diamond_branch() {
        let source = r#"
            pc
            calldataload
            push1 target
            jumpi

            push1 exit
            jump

            target:
                jumpdest
                push1 exit
                jump

            exit:
                jumpdest
        "#;

        CfgTest {
            source,
            connected: &[
                (0, N::Offset(5)),
                (0, N::Offset(8)),
                (5, N::Offset(12)),
                (8, N::Offset(12)),
                (12, N::Terminate),
            ],
            unconnected: &[
                (0, N::Offset(0)),
                (0, N::Offset(12)),
                (0, N::BadJump),
                (0, N::Terminate),
                (5, N::Offset(0)),
                (5, N::Offset(5)),
                (5, N::Offset(8)),
                (5, N::BadJump),
                (5, N::Terminate),
                (8, N::Offset(0)),
                (8, N::Offset(8)),
                (8, N::Offset(5)),
                (8, N::BadJump),
                (8, N::Terminate),
                (12, N::Offset(0)),
                (12, N::Offset(8)),
                (12, N::Offset(5)),
                (12, N::Offset(12)),
                (12, N::BadJump),
            ],
        }
        .check();
    }

    #[test]
    fn memory_jump() {
        let source = r#"
            push1 target
            push1 0
            mstore
            push1 0
            mload
            jump

            target:
                jumpdest
        "#;

        CfgTest {
            source,
            connected: &[(0, N::Offset(9)), (9, N::Terminate)],
            unconnected: &[
                // TODO: Until the memory stuff is better, can't prove:
                // (0, N::BadJump),
                (0, N::Terminate),
                (9, N::BadJump),
                (9, N::Offset(0)),
            ],
        }
        .check();
    }

    #[test]
    fn storage_jump() {
        let source = r#"
            push1 target
            push1 0
            sstore
            push1 0
            sload
            jump

            target:
                jumpdest
        "#;

        CfgTest {
            source,
            connected: &[(0, N::Offset(9)), (9, N::Terminate)],
            unconnected: &[
                // TODO: Until the storage stuff is better, can't prove:
                // (0, N::BadJump),
                (0, N::Terminate),
                (9, N::BadJump),
                (9, N::Offset(0)),
            ],
        }
        .check();
    }

    #[test]
    fn shr_branch() {
        let source = r#"
            push32 0x23b872dd00000000000000000000000000000000000000000000000000000000
            push1 224
            shr
            push4 0x23b872dd
            eq
            push4 transfer_from
            jumpi

            stop

            transfer_from:
            jumpdest
            stop
        "#;

        CfgTest {
            source,
            connected: &[
                (0, N::Offset(0x31)),
                (0x30, N::Terminate),
                (0x31, N::Terminate),
            ],
            unconnected: &[
                (0, N::Offset(0)),
                (0, N::Offset(0x30)),
                (0, N::BadJump),
                (0, N::Terminate),
                (0x30, N::Offset(0x30)),
                (0x30, N::Offset(0x31)),
                (0x30, N::Offset(0)),
                (0x30, N::BadJump),
                (0x31, N::Offset(0x31)),
                (0x31, N::Offset(0x30)),
                (0x31, N::Offset(0)),
                (0x31, N::BadJump),
            ],
        }
        .check();
    }
}
