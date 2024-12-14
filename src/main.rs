use plonky2::{
    field::{
        goldilocks_field::GoldilocksField as F,
        types::{Field, PrimeField64},
    }, hash::hash_types::{HashOutTarget, MerkleCapTarget}, iop::{
        generator::{GeneratedValues, SimpleGenerator},
        target::Target,
        witness::{PartialWitness, PartitionWitness, WitnessWrite},
    }, plonk::{
        circuit_builder::CircuitBuilder,
        circuit_data::{CircuitConfig, CircuitData, CommonCircuitData, VerifierCircuitTarget, VerifierOnlyCircuitData},
        config::PoseidonGoldilocksConfig,
        proof::{ProofWithPublicInputs, ProofWithPublicInputsTarget},
    }, recursion::cyclic_recursion::check_cyclic_proof_verifier_data, util::serialization::{Buffer, IoResult, Read, Write}
};

use anyhow::Result;

type C = PoseidonGoldilocksConfig;
const D: usize = 2;

/// A simplified 2048 circuit. In a real implementation, add proper move constraints.
#[derive(Debug)]
struct Game2048Circuit;

impl Game2048Circuit {
    /// Builds a base circuit for verifying a single move in the 2048 game.
    /// Returns (builder, targets) where targets are:
    ///  - 16 before-board targets
    ///  - 16 after-board targets
    ///  - 1 direction target
    pub fn build_circuit() -> (CircuitBuilder<F, D>, Vec<Target>) {
        let config = CircuitConfig::standard_recursion_config();
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

        builder.print_gate_counts(0);
        (builder, targets)
    }

    /// Add constraints to ensure the move from before_board to after_board is valid.
    /// For simplicity, we won't implement full 2048 rules here—just placeholder constraints.
    pub fn add_constraints(
        builder: &mut CircuitBuilder<F, D>,
        before_board: &[Target],
        after_board: &[Target],
        direction: Target,
    ) {
        // Add range checks for all inputs
        for &t in before_board.iter().chain(after_board.iter()) {
            builder.range_check(t, 32);  // Assuming values are 32-bit
        }
        builder.range_check(direction, 2);  // 0-3 for directions

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

/// Recursive circuit that can verify a previous proof and a current move.
#[derive(Debug)]
struct RecursiveGame2048Circuit {
    circuit: CircuitData<F, C, D>,
    recursive_proof_target: ProofWithPublicInputsTarget<D>,
    before_board_targets: Vec<Target>,
    after_board_targets: Vec<Target>,
    direction_target: Target,
}

impl RecursiveGame2048Circuit {
    pub fn build_recursive_circuit(
        previous_circuit: Option<&CircuitData<F, C, D>>,
    ) -> Self {
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config.clone());

        // Add previous proof target if any
        let (recursive_proof_target, verifier_data) = if let Some(prev_circuit) = previous_circuit {
            let proof_target = builder.add_virtual_proof_with_pis(&prev_circuit.common);
            let verifier_data = builder.add_virtual_verifier_data(prev_circuit.common.config.fri_config.cap_height);
            
            // Add generator for verifier data
            builder.add_simple_generator(VerifierDataGenerator {
                verifier_data_target: verifier_data.clone(),
                verifier_data: prev_circuit.verifier_only.clone(),
            });
            
            (proof_target, verifier_data)
        } else {
            // Create a base circuit for the base case
            let (base_builder, _) = Game2048Circuit::build_circuit();
            let base_data = base_builder.build::<C>();
            let proof_target = builder.add_virtual_proof_with_pis(&base_data.common);
            let verifier_data = builder.add_virtual_verifier_data(base_data.common.config.fri_config.cap_height);
            
            // Add generator for verifier data
            builder.add_simple_generator(VerifierDataGenerator {
                verifier_data_target: verifier_data.clone(),
                verifier_data: base_data.verifier_only,
            });
            
            (proof_target, verifier_data)
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
            builder.verify_proof::<C>(&recursive_proof_target, &verifier_data, &prev_circuit.common);
        }

        // Add constraints for current move
        Game2048Circuit::add_constraints(
            &mut builder,
            &before_board_targets,
            &after_board_targets,
            direction_target,
        );

        builder.print_gate_counts(0);
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
        previous_proof: Option<ProofWithPublicInputs<F, C, D>>,
        before_board: Vec<F>,
        after_board: Vec<F>,
        direction: F,
    ) -> anyhow::Result<ProofWithPublicInputs<F, C, D>> {
        // Validate input sizes
        if before_board.len() != 16 {
            anyhow::bail!("Before board must have exactly 16 elements");
        }
        if after_board.len() != 16 {
            anyhow::bail!("After board must have exactly 16 elements");
        }
        
        // Validate direction
        let dir_val = direction.to_canonical_u64();
        if dir_val > 3 {
            anyhow::bail!("Direction must be 0 (up), 1 (down), 2 (left), or 3 (right)");
        }

        let mut pw = PartialWitness::<F>::new();

        // Set previous proof witness if any
        if let Some(proof) = previous_proof {
            pw.set_proof_with_pis_target(&self.recursive_proof_target, &proof)?;
        }

        // Set current move
        for (i, &target) in self.before_board_targets.iter().enumerate() {
            pw.set_target(target, before_board[i])?;
        }
        for (i, &target) in self.after_board_targets.iter().enumerate() {
            pw.set_target(target, after_board[i])?;
        }
        pw.set_target(self.direction_target, direction)?;

        self.circuit.prove(pw)
    }

    pub fn verify(
        &self,
        proof: ProofWithPublicInputs<F, C, D>,
    ) -> anyhow::Result<()> {
        // Validate public inputs length
        let expected_inputs = 33; // 16 before + 16 after + 1 direction
        if proof.public_inputs.len() != expected_inputs {
            anyhow::bail!(
                "Invalid number of public inputs. Expected {}, got {}",
                expected_inputs,
                proof.public_inputs.len()
            );
        }

        // Validate direction value
        let direction = proof.public_inputs[32].to_canonical_u64();
        if direction > 3 {
            anyhow::bail!("Invalid direction value in proof: {}", direction);
        }

        // First verify the proof itself
        self.circuit.verify(proof.clone())?;

        // Then verify the cyclic proof verifier data
        check_cyclic_proof_verifier_data(&proof, &self.circuit.verifier_only, &self.circuit.common)
    }
}

#[derive(Debug)]
struct VerifierDataGenerator {
    verifier_data_target: VerifierCircuitTarget,
    verifier_data: VerifierOnlyCircuitData<C, D>,
}

impl SimpleGenerator<F, D> for VerifierDataGenerator {
    fn id(&self) -> String {
        "VerifierDataGenerator".to_string()
    }

    fn dependencies(&self) -> Vec<Target> {
        vec![]
    }

    fn run_once(&self, _witness: &PartitionWitness<F>, out_buffer: &mut GeneratedValues<F>) -> anyhow::Result<()> {
        out_buffer.set_verifier_data_target(&self.verifier_data_target, &self.verifier_data);
        Ok(())
    }

    fn serialize(&self, dst: &mut Vec<u8>, _common_data: &CommonCircuitData<F, D>) -> IoResult<()> {
        // Serialize the verifier data target
        let cap_targets = &self.verifier_data_target.constants_sigmas_cap.0;
        dst.write_usize(cap_targets.len())?;
        for hash_out in cap_targets {
            for &element in &hash_out.elements {
                dst.write_target(element)?;
            }
        }

        // Serialize circuit digest
        for &element in &self.verifier_data_target.circuit_digest.elements {
            dst.write_target(element)?;
        }
        
        // Serialize verifier data
        let verifier_bytes = self.verifier_data.to_bytes()?;
        dst.write_usize(verifier_bytes.len())?;
        dst.extend_from_slice(&verifier_bytes);
        Ok(())
    }

    fn deserialize(src: &mut Buffer, _common_data: &CommonCircuitData<F, D>) -> IoResult<Self> {
        // Deserialize MerkleCapTarget
        let cap_len = src.read_usize()?;
        let mut cap_targets = Vec::with_capacity(cap_len);
        for _ in 0..cap_len {
            let mut elements = [Target::default(); 4];
            for element in &mut elements {
                *element = src.read_target()?;
            }
            cap_targets.push(HashOutTarget { elements });
        }
        let constants_sigmas_cap = MerkleCapTarget(cap_targets);

        // Deserialize HashOutTarget
        let mut elements = [Target::default(); 4];
        for element in &mut elements {
            *element = src.read_target()?;
        }
        let circuit_digest = HashOutTarget { elements };

        // Create VerifierCircuitTarget
        let verifier_data_target = VerifierCircuitTarget {
            constants_sigmas_cap,
            circuit_digest,
        };

        // Deserialize VerifierOnlyCircuitData
        let data_len = src.read_usize()?;
        let mut data_bytes = vec![0u8; data_len];
        src.read_exact(&mut data_bytes)?;
        let verifier_data = VerifierOnlyCircuitData::from_bytes(data_bytes)?;

        Ok(Self {
            verifier_data_target,
            verifier_data,
        })
    }
}

/// Main function demonstrating the 2048 game circuit proof generation and verification
fn main() -> Result<()> {
    // Input boards and direction
    let before_board: Vec<F> = vec![
        F::from_canonical_u32(2), F::from_canonical_u32(2), F::from_canonical_u32(4), F::from_canonical_u32(8),
        F::from_canonical_u32(2), F::ZERO,                  F::from_canonical_u32(4), F::from_canonical_u32(4),
        F::from_canonical_u32(2), F::from_canonical_u32(2), F::from_canonical_u32(2), F::from_canonical_u32(4),
        F::ZERO,                  F::from_canonical_u32(2), F::from_canonical_u32(4), F::from_canonical_u32(4),
    ];

    let after_board: Vec<F> = vec![
        F::ZERO, F::from_canonical_u32(4), F::from_canonical_u32(4), F::from_canonical_u32(8),
        F::ZERO, F::ZERO,                  F::from_canonical_u32(2), F::from_canonical_u32(8),
        F::ZERO, F::from_canonical_u32(2), F::from_canonical_u32(4), F::from_canonical_u32(4),
        F::ZERO, F::ZERO,                  F::from_canonical_u32(2), F::from_canonical_u32(8),
    ];

    // Direction: "right" (3)
    let direction = F::from_canonical_u32(3);

    // Build the circuit
    let (circuit_builder, targets) = Game2048Circuit::build_circuit();

    // Unpack targets
    let (before_targets, after_targets, direction_target) =
        (&targets[0..16], &targets[16..32], targets[32]);

    // Set the witness values
    let mut pw = PartialWitness::<F>::new();
    
    // Set before board values
    for (i, &target) in before_targets.iter().enumerate() {
        pw.set_target(target, before_board[i])?;
    }
    
    // Set after board values
    for (i, &target) in after_targets.iter().enumerate() {
        pw.set_target(target, after_board[i])?;
    }
    
    // Set direction
    pw.set_target(direction_target, direction)?;

    // Build and generate the proof
    let circuit = circuit_builder.build::<PoseidonGoldilocksConfig>();
    let proof = circuit.prove(pw)?;

    // Verify the proof
    circuit.verify(proof)?;
    println!("Proof verified successfully!");

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_recursive_game2048_multiple_states() -> anyhow::Result<()> {
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
            pw1.set_target(target, before_board1[i]);
        }
        for (i, &target) in after_board_targets1.iter().enumerate() {
            pw1.set_target(target, after_board1[i]);
        }
        pw1.set_target(direction_target1, direction1);
        let proof1 = base_circuit.prove(pw1)?;
        base_circuit.verify(proof1.clone())?;

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
        let proof2 = recursive_circuit1.prove(Some(proof1), before_board2, after_board2.clone(), direction2)?;
        recursive_circuit1.verify(proof2.clone())?;

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
        let proof3 = recursive_circuit2.prove(Some(proof2), before_board3, after_board3, direction3)?;
        recursive_circuit2.verify(proof3.clone())?;

        Ok(())
    }
}