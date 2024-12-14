use plonky2::{
    field::goldilocks_field::GoldilocksField as F,
    field::types::Field,
    hash::hash_types::RichField,
    iop::target::Target,
    iop::witness::PartialWitness,
    plonk::{
        circuit_builder::CircuitBuilder,
        circuit_data::{CircuitConfig, CircuitData},
        config::{AlgebraicHasher, GenericConfig, PoseidonGoldilocksConfig},
    },
    recursion::{
        recursive_circuit::{add_virtual_recursive_proof_target, build_recursive_circuit, RecursiveProofTarget},
        verifier_circuit::verify_proof_target,
    },
};

type C = PoseidonGoldilocksConfig;
const D: usize = 2;

// A simplified 2048 circuit. In a real implementation, add proper move constraints.
struct Game2048Circuit;

impl Game2048Circuit {
    /// Builds a base circuit for verifying a single move in the 2048 game.
    /// Returns (builder, targets) where targets are:
    ///  - 16 before-board targets
    ///  - 16 after-board targets
    ///  - 1 direction target
    pub fn build_circuit() -> (CircuitBuilder<F, D>, Vec<Target>) {
        let config = CircuitConfig::standard_ecc_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        // 16 before + 16 after + 1 direction = 33 total public inputs
        let mut targets = vec![];
        for _ in 0..16 {
            let t = builder.add_virtual_target();
            builder.register_public_input(t);
            targets.push(t);
        }
        for _ in 0..16 {
            let t = builder.add_virtual_target();
            builder.register_public_input(t);
            targets.push(t);
        }
        let direction_t = builder.add_virtual_target();
        builder.register_public_input(direction_t);
        targets.push(direction_t);

        // Add constraints for a valid move
        Self::add_constraints(&mut builder, &targets[0..16], &targets[16..32], targets[32]);

        (builder, targets)
    }

    /// Add constraints to ensure the move from before_board to after_board is valid.
    /// For simplicity, we won't implement full 2048 rules here—just placeholder constraints.
    pub fn add_constraints(
        builder: &mut CircuitBuilder<F, D>,
        before_board: &[Target],
        after_board: &[Target],
        _direction: Target,
    ) {
        // Placeholder constraints: sum(before_board) = sum(after_board)
        let mut before_sum = builder.zero();
        for &b in before_board {
            before_sum = builder.add(before_sum, b);
        }
        let mut after_sum = builder.zero();
        for &a in after_board {
            after_sum = builder.add(after_sum, a);
        }
        builder.connect(before_sum, after_sum);
    }
}

// Recursive circuit that can verify a previous proof and a current move.
struct RecursiveGame2048Circuit {
    circuit: CircuitData<F, C, D>,
    recursive_proof_target: RecursiveProofTarget<F, C, D>,
    before_board_targets: Vec<Target>,
    after_board_targets: Vec<Target>,
    direction_target: Target,
}

impl RecursiveGame2048Circuit {
    pub fn build_recursive_circuit(
        previous_circuit: Option<&CircuitData<F, C, D>>,
    ) -> Self {
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        // Add previous proof target if any
        let recursive_proof_target = if let Some(prev_circuit) = previous_circuit {
            add_virtual_recursive_proof_target(&mut builder, prev_circuit)
        } else {
            // If no previous circuit, create a dummy target
            // In practice, you'd handle the "no previous proof" case differently.
            let dummy = build_recursive_circuit(&mut builder, None::<CircuitData<F, C, D>>);
            dummy
        };

        // Current move inputs
        let before_board_targets: Vec<_> = (0..16).map(|_| builder.add_virtual_target()).collect();
        let after_board_targets: Vec<_> = (0..16).map(|_| builder.add_virtual_target()).collect();
        let direction_target = builder.add_virtual_target();

        // Register as public inputs
        for &t in &before_board_targets {
            builder.register_public_input(t);
        }
        for &t in &after_board_targets {
            builder.register_public_input(t);
        }
        builder.register_public_input(direction_target);

        // Verify previous proof if given
        if let Some(prev_circuit) = previous_circuit {
            verify_proof_target(&mut builder, &recursive_proof_target, prev_circuit);
        }

        // Add constraints for current move
        Game2048Circuit::add_constraints(
            &mut builder,
            &before_board_targets,
            &after_board_targets,
            direction_target,
        );

        let circuit = builder.build::<C>();

        Self {
            circuit,
            recursive_proof_target,
            before_board_targets,
            after_board_targets,
            direction_target,
        }
    }

    pub fn prove(
        &self,
        previous_proof: Option<plonky2::plonk::proof::ProofWithPublicInputs<F, C, D>>,
        before_board: Vec<F>,
        after_board: Vec<F>,
        direction: F,
    ) -> plonky2::plonk::proof::ProofWithPublicInputs<F, C, D> {
        let mut pw = PartialWitness::<F>::new();

        // Set previous proof witness if any
        if let Some(proof) = previous_proof {
            pw.set_recursive_proof_target(&self.recursive_proof_target, &proof);
        }

        // Set current move
        for (i, &target) in self.before_board_targets.iter().enumerate() {
            pw.set_target(target, before_board[i]).unwrap();
        }
        for (i, &target) in self.after_board_targets.iter().enumerate() {
            pw.set_target(target, after_board[i]).unwrap();
        }
        pw.set_target(self.direction_target, direction).unwrap();

        self.circuit.prove(pw).unwrap()
    }

    pub fn verify(
        &self,
        proof: plonky2::plonk::proof::ProofWithPublicInputs<F, C, D>,
    ) -> bool {
        self.circuit.verify(proof).is_ok()
    }
}

fn main() {
    // Example usage in main
    // Initial board and move
    let before_board1: Vec<F> = vec![
        F::from_canonical_u32(2), F::from_canonical_u32(2), F::ZERO,                    F::from_canonical_u32(4),
        F::ZERO,                  F::ZERO,                  F::from_canonical_u32(4),   F::ZERO,
        F::from_canonical_u32(2), F::ZERO,                  F::ZERO,                    F::from_canonical_u32(2),
        F::ZERO,                  F::from_canonical_u32(4), F::ZERO,                    F::ZERO,
    ];

    let after_board1: Vec<F> = vec![
        F::from_canonical_u32(4),   F::from_canonical_u32(2),   F::from_canonical_u32(4),   F::from_canonical_u32(4),
        F::ZERO,                    F::from_canonical_u32(4),   F::ZERO,                    F::from_canonical_u32(2),
        F::ZERO,                    F::ZERO,                    F::ZERO,                    F::ZERO,
        F::ZERO,                    F::ZERO,                    F::ZERO,                    F::ZERO,
    ];
    let direction1 = F::from_canonical_u32(0); // "up"

    // Build base circuit and prove first move
    let (base_builder, base_targets) = Game2048Circuit::build_circuit();
    let base_circuit = base_builder.build::<C>();

    let mut pw1 = PartialWitness::<F>::new();
    let before_board_targets1 = &base_targets[0..16];
    let after_board_targets1 = &base_targets[16..32];
    let direction_target1 = base_targets[32];

    for (i, &target) in before_board_targets1.iter().enumerate() {
        pw1.set_target(target, before_board1[i]).unwrap();
    }
    for (i, &target) in after_board_targets1.iter().enumerate() {
        pw1.set_target(target, after_board1[i]).unwrap();
    }
    pw1.set_target(direction_target1, direction1).unwrap();

    let proof1 = base_circuit.prove(pw1).unwrap();
    assert!(base_circuit.verify(proof1.clone()).is_ok(), "Base proof verification failed");

    // Second move
    let before_board2: Vec<F> = after_board1.clone(); // Use after_board1 as before_board2
    let after_board2: Vec<F> = vec![
        F::from_canonical_u32(4),   F::ZERO,   F::from_canonical_u32(4),   F::from_canonical_u32(4),
        F::from_canonical_u32(2),   F::from_canonical_u32(4),   F::ZERO,                    F::from_canonical_u32(2),
        F::ZERO,                    F::ZERO,                    F::ZERO,                    F::ZERO,
        F::ZERO,                    F::ZERO,                    F::ZERO,                    F::ZERO,
    ];
    let direction2 = F::from_canonical_u32(3); // "right"

    // Recursive circuit #1
    let recursive_circuit1 = RecursiveGame2048Circuit::build_recursive_circuit(Some(&base_circuit));

    // Generate recursive proof for second move
    let proof2 = recursive_circuit1.prove(Some(proof1), before_board2.clone(), after_board2.clone(), direction2);
    assert!(recursive_circuit1.verify(proof2.clone()), "Recursive proof verification failed");
    println!("Recursive proof verified! 🎉");

    // Third move
    let before_board3: Vec<F> = after_board2.clone(); // Use after_board2 as before_board3
    let after_board3: Vec<F> = vec![
        F::from_canonical_u32(4),   F::from_canonical_u32(4),   F::from_canonical_u32(4),   F::ZERO,
        F::from_canonical_u32(2),   F::from_canonical_u32(4),   F::from_canonical_u32(2),   F::ZERO,
        F::ZERO,                    F::ZERO,                    F::ZERO,                    F::ZERO,
        F::ZERO,                    F::ZERO,                    F::ZERO,                    F::ZERO,
    ];
    let direction3 = F::from_canonical_u32(2); // "left"

    // Recursive circuit #2
    let recursive_circuit2 = RecursiveGame2048Circuit::build_recursive_circuit(Some(&recursive_circuit1.circuit));

    // Generate second recursive proof for the third move
    let proof3 = recursive_circuit2.prove(Some(proof2), before_board3, after_board3, direction3);
    assert!(recursive_circuit2.verify(proof3.clone()), "Second recursive proof verification failed");
    println!("Second recursive proof verified! 🎉🎉");
}

#[cfg(test)]
mod tests {
    use super::*;
    use plonky2::iop::witness::PartialWitness;

    #[test]
    fn test_recursive_game2048_multiple_states() {
        // Build the base circuit
        let (base_builder, base_targets) = Game2048Circuit::build_circuit();
        let base_circuit = base_builder.build::<C>();

        // Initial board
        let before_board1: Vec<F> = vec![
            F::from_canonical_u32(2), F::from_canonical_u32(2), F::ZERO,                    F::from_canonical_u32(4),
            F::ZERO,                  F::ZERO,                  F::from_canonical_u32(4),   F::ZERO,
            F::from_canonical_u32(2), F::ZERO,                  F::ZERO,                    F::from_canonical_u32(2),
            F::ZERO,                  F::from_canonical_u32(4), F::ZERO,                    F::ZERO,
        ];

        let after_board1: Vec<F> = vec![
            F::from_canonical_u32(4),   F::from_canonical_u32(2),   F::from_canonical_u32(4),   F::from_canonical_u32(4),
            F::ZERO,                    F::from_canonical_u32(4),   F::ZERO,                    F::from_canonical_u32(2),
            F::ZERO,                    F::ZERO,                    F::ZERO,                    F::ZERO,
            F::ZERO,                    F::ZERO,                    F::ZERO,                    F::ZERO,
        ];
        let direction1 = F::from_canonical_u32(0); // "up"

        // Prove the first move
        let mut pw1 = PartialWitness::<F>::new();
        let before_board_targets1 = &base_targets[0..16];
        let after_board_targets1 = &base_targets[16..32];
        let direction_target1 = base_targets[32];
        for (i, &target) in before_board_targets1.iter().enumerate() {
            pw1.set_target(target, before_board1[i]).unwrap();
        }
        for (i, &target) in after_board_targets1.iter().enumerate() {
            pw1.set_target(target, after_board1[i]).unwrap();
        }
        pw1.set_target(direction_target1, direction1).unwrap();
        let proof1 = base_circuit.prove(pw1).unwrap();
        assert!(base_circuit.verify(proof1.clone()).is_ok());

        // Prepare second move (recursive)
        let before_board2: Vec<F> = after_board1.clone();
        let after_board2: Vec<F> = vec![
            F::from_canonical_u32(4),   F::ZERO,   F::from_canonical_u32(4),   F::from_canonical_u32(4),
            F::from_canonical_u32(2),   F::from_canonical_u32(4),   F::ZERO,                    F::from_canonical_u32(2),
            F::ZERO,                    F::ZERO,                    F::ZERO,                    F::ZERO,
            F::ZERO,                    F::ZERO,                    F::ZERO,                    F::ZERO,
        ];
        let direction2 = F::from_canonical_u32(3); // "right"

        // Recursive circuit #1
        let recursive_circuit1 = RecursiveGame2048Circuit::build_recursive_circuit(Some(&base_circuit));
        let proof2 = recursive_circuit1.prove(Some(proof1), before_board2, after_board2.clone(), direction2);
        assert!(recursive_circuit1.verify(proof2.clone()));

        // Third move (second recursion)
        let before_board3: Vec<F> = after_board2.clone();
        let after_board3: Vec<F> = vec![
            F::from_canonical_u32(4),   F::from_canonical_u32(4),   F::from_canonical_u32(4),   F::ZERO,
            F::from_canonical_u32(2),   F::from_canonical_u32(4),   F::from_canonical_u32(2),   F::ZERO,
            F::ZERO,                    F::ZERO,                    F::ZERO,                    F::ZERO,
            F::ZERO,                    F::ZERO,                    F::ZERO,                    F::ZERO,
        ];
        let direction3 = F::from_canonical_u32(2); // "left"

        // Recursive circuit #2
        let recursive_circuit2 = RecursiveGame2048Circuit::build_recursive_circuit(Some(&recursive_circuit1.circuit));
        let proof3 = recursive_circuit2.prove(Some(proof2), before_board3, after_board3, direction3);
        assert!(recursive_circuit2.verify(proof3));
    }
}