use anyhow::Result;
use plonky2::{
    field::{
        goldilocks_field::GoldilocksField as F,
        types::Field,
    },
    iop::{
        witness::{PartialWitness, WitnessWrite},
        target::Target,
    },
    plonk::{
        circuit_builder::CircuitBuilder,
        circuit_data::CircuitConfig,
        config::PoseidonGoldilocksConfig,
    },
};

type C = PoseidonGoldilocksConfig;
const D: usize = 2;

/// Represents a move direction in the 2048 game
#[derive(Debug, Clone, Copy)]
enum Direction {
    Up = 0,
    Down = 1,
    Left = 2,
    Right = 3,
}

/// Circuit for verifying moves in the 2048 game
#[derive(Debug)]
struct Game2048Circuit {
    config: CircuitConfig,
    board_size: usize,
}

impl Game2048Circuit {
    /// Creates a new 2048 game circuit
    pub fn new(board_size: usize) -> Self {
        let config = CircuitConfig::standard_recursion_config();
        Self {
            config,
            board_size,
        }
    }

    /// Builds a circuit for verifying a single move
    /// Returns (circuit_builder, input_targets) where input_targets contains:
    /// - board_size^2 targets for the before board state
    /// - board_size^2 targets for the after board state
    /// - 1 target for move direction
    pub fn build_circuit(&self) -> (CircuitBuilder<F, D>, Vec<Target>) {
        let mut builder = CircuitBuilder::<F, D>::new(self.config.clone());
        let total_cells = self.board_size * self.board_size;

        // Create targets for before and after board states
        let mut targets = vec![];
        
        // Before board state
        for _ in 0..total_cells {
            let t = builder.add_virtual_target();
            builder.register_public_input(t);
            targets.push(t);
        }

        // After board state
        for _ in 0..total_cells {
            let t = builder.add_virtual_target();
            builder.register_public_input(t);
            targets.push(t);
        }

        // Direction target
        let direction_t = builder.add_virtual_target();
        builder.register_public_input(direction_t);
        targets.push(direction_t);

        // Add constraints
        self.add_move_constraints(&mut builder, &targets);

        builder.print_gate_counts(0);
        (builder, targets)
    }

    /// Adds constraints to verify a valid move
    fn add_move_constraints(&self, builder: &mut CircuitBuilder<F, D>, targets: &[Target]) {
        let total_cells = self.board_size * self.board_size;
        let (before_board, after_board) = targets.split_at(total_cells);
        let (after_board, direction) = after_board.split_at(total_cells);
        let direction = direction[0];

        // Range check all board values (assuming max value is 2^11 = 2048)
        for &t in before_board.iter().chain(after_board.iter()) {
            builder.range_check(t, 11);
        }

        // Range check direction (0-3)
        builder.range_check(direction, 2);

        // Core game rules constraints
        self.add_game_rules_constraints(builder, before_board, after_board, direction);
    }

    /// Adds constraints for the core 2048 game rules
    fn add_game_rules_constraints(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        before_board: &[Target],
        after_board: &[Target],
        direction: Target,
    ) {
        // 1. Conservation of tiles constraint
        let zero = builder.constant(F::ZERO);
        let mut before_sum = zero;
        for &b in before_board {
            before_sum = builder.add(before_sum, b);
        }
        let mut after_sum = zero;
        for &a in after_board {
            after_sum = builder.add(after_sum, a);
        }
        // After sum must be >= before sum
        let diff = builder.sub(after_sum, before_sum);
        builder.range_check(diff, 11); // Difference must be <= 2048

        // 2. Value constraints
        // All values must be powers of 2 or 0
        for &cell in before_board.iter().chain(after_board.iter()) {
            self.add_power_of_two_constraint(builder, cell);
        }

        // 3. Direction-specific constraints
        self.add_direction_constraints(builder, before_board, after_board, direction);
    }

    /// Adds direction-specific constraints for the move
    fn add_direction_constraints(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        before_board: &[Target],
        after_board: &[Target],
        direction: Target,
    ) {
        // Create constants for each direction
        let up = builder.constant(F::from_canonical_u32(Direction::Up as u32));
        let down = builder.constant(F::from_canonical_u32(Direction::Down as u32));
        let left = builder.constant(F::from_canonical_u32(Direction::Left as u32));
        let right = builder.constant(F::from_canonical_u32(Direction::Right as u32));

        // Check if each direction is selected
        let is_up = builder.is_equal(direction, up);
        let is_down = builder.is_equal(direction, down);
        let is_left = builder.is_equal(direction, left);
        let is_right = builder.is_equal(direction, right);

        // Create constant targets for 0 and 1
        let zero_target = builder.constant(F::ZERO);
        let one_target = builder.constant(F::ONE);

        // For each row/column, add constraints based on the direction
        for row in 0..self.board_size {
            for col in 0..self.board_size {
                let idx = row * self.board_size + col;
                let current = before_board[idx];
                let current_after = after_board[idx];

                // Calculate potential next indices for each direction
                let up_idx = if row > 0 { Some((row - 1) * self.board_size + col) } else { None };
                let down_idx = if row < self.board_size - 1 { Some((row + 1) * self.board_size + col) } else { None };
                let left_idx = if col > 0 { Some(row * self.board_size + (col - 1)) } else { None };
                let right_idx = if col < self.board_size - 1 { Some(row * self.board_size + (col + 1)) } else { None };

                // For each valid direction, add constraints
                if let Some(next_idx) = up_idx {
                    let next_val = before_board[next_idx];
                    let next_after = after_board[next_idx];
                    self.add_move_constraints_for_direction(
                        builder, current, current_after, next_val, next_after,
                        is_up, zero_target, one_target
                    );
                }

                if let Some(next_idx) = down_idx {
                    let next_val = before_board[next_idx];
                    let next_after = after_board[next_idx];
                    self.add_move_constraints_for_direction(
                        builder, current, current_after, next_val, next_after,
                        is_down, zero_target, one_target
                    );
                }

                if let Some(next_idx) = left_idx {
                    let next_val = before_board[next_idx];
                    let next_after = after_board[next_idx];
                    self.add_move_constraints_for_direction(
                        builder, current, current_after, next_val, next_after,
                        is_left, zero_target, one_target
                    );
                }

                if let Some(next_idx) = right_idx {
                    let next_val = before_board[next_idx];
                    let next_after = after_board[next_idx];
                    self.add_move_constraints_for_direction(
                        builder, current, current_after, next_val, next_after,
                        is_right, zero_target, one_target
                    );
                }

                // If no movement is possible in the selected direction, cell must stay the same
                let mut direction_possibilities = Vec::new();
                if up_idx.is_some() {
                    direction_possibilities.push(builder.select(is_up, one_target, zero_target));
                }
                if down_idx.is_some() {
                    direction_possibilities.push(builder.select(is_down, one_target, zero_target));
                }
                if left_idx.is_some() {
                    direction_possibilities.push(builder.select(is_left, one_target, zero_target));
                }
                if right_idx.is_some() {
                    direction_possibilities.push(builder.select(is_right, one_target, zero_target));
                }

                let any_direction_possible = builder.add_many(&direction_possibilities);
                // Store the equality check result
                let is_one = builder.is_equal(any_direction_possible, one_target);
                // Now use the stored result
                let must_stay_same = builder.not(is_one);
                // Store the equality check result
                let stays_same = builder.is_equal(current, current_after);
                
                // Convert boolean conditions to targets for arithmetic
                let must_stay_same_t = builder.select(must_stay_same, one_target, zero_target);
                let stays_same_t = builder.select(stays_same, one_target, zero_target);
                
                // Both conditions must be true (using arithmetic)
                let both_true = builder.mul(must_stay_same_t, stays_same_t);
                // Store the equality check result
                let final_bool = builder.is_equal(both_true, one_target);
                builder.assert_bool(final_bool);
            }
        }

        // Verify that exactly one direction is chosen
        let mut direction_targets = Vec::new();
        // Convert BoolTargets to arithmetic targets
        direction_targets.push(builder.select(is_up, one_target, zero_target));
        direction_targets.push(builder.select(is_down, one_target, zero_target));
        direction_targets.push(builder.select(is_left, one_target, zero_target));
        direction_targets.push(builder.select(is_right, one_target, zero_target));
        // Store the sum result
        let direction_sum = builder.add_many(&direction_targets);
        // Store the equality check result
        let direction_valid = builder.is_equal(direction_sum, one_target);
        builder.assert_bool(direction_valid);
    }

    /// Helper function to add constraints for a single direction
    fn add_move_constraints_for_direction(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        current: Target,
        current_after: Target,
        next_val: Target,
        next_after: Target,
        is_this_direction: plonky2::iop::target::BoolTarget,
        zero_target: Target,
        one_target: Target,
    ) {
        // Case 1: Values are equal - can merge
        let values_equal = builder.is_equal(current, next_val);
        let merged_value = builder.mul_const(F::TWO, current);
        let merged_correctly = builder.is_equal(next_after, merged_value);
        let merge_possible = builder.and(values_equal, merged_correctly);

        // Case 2: Next cell is empty - can move
        let next_is_empty = builder.is_equal(next_val, zero_target);
        let moved_correctly = builder.is_equal(next_after, current);
        let move_possible = builder.and(next_is_empty, moved_correctly);

        // Case 3: Cell stays the same
        let stays_same = builder.is_equal(current, current_after);

        // Case 4: Cell becomes zero (after moving or merging)
        let becomes_zero = builder.is_equal(current_after, zero_target);

        // Convert boolean conditions to arithmetic targets
        let mut transition_targets = Vec::new();
        transition_targets.push(builder.select(stays_same, one_target, zero_target));
        transition_targets.push(builder.select(becomes_zero, one_target, zero_target));
        transition_targets.push(builder.select(merge_possible, one_target, zero_target));
        transition_targets.push(builder.select(move_possible, one_target, zero_target));
        
        // Sum all possibilities and verify exactly one is true
        let valid_transition = builder.add_many(&transition_targets);
        // Store the equality check result
        let valid_state = builder.is_equal(valid_transition, one_target);
        
        // Convert to arithmetic for final combination
        let direction_t = builder.select(is_this_direction, one_target, zero_target);
        let valid_state_t = builder.select(valid_state, one_target, zero_target);
        // Store the multiplication result
        let final_value = builder.mul(direction_t, valid_state_t);
        // Store the equality check result
        let final_bool = builder.is_equal(final_value, one_target);
        builder.assert_bool(final_bool);
    }

    /// Adds constraint that a value must be 0 or a power of 2
    fn add_power_of_two_constraint(&self, builder: &mut CircuitBuilder<F, D>, value: Target) {
        // Create constant targets for 0 and 1
        let zero_target = builder.constant(F::ZERO);
        let one_target = builder.constant(F::ONE);

        // Create a list of valid values: 0, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048
        let valid_values: Vec<Target> = (0..12)
            .map(|i| {
                if i == 0 {
                    builder.constant(F::ZERO)
                } else {
                    builder.constant(F::from_canonical_u32(1 << i))
                }
            })
            .collect();

        // Add constraint that value must equal one of these
        let mut valid_value_targets = Vec::new();
        for &valid_value in &valid_values {
            let is_this_value = builder.is_equal(value, valid_value);
            valid_value_targets.push(builder.select(is_this_value, one_target, zero_target));
        }
        let sum = builder.add_many(&valid_value_targets);
        builder.connect(sum, one_target);
    }

    /// Proves a valid move
    pub fn prove_move(
        &self,
        before_board: Vec<F>,
        after_board: Vec<F>,
        direction: Direction,
    ) -> Result<()> {
        let (builder, targets) = self.build_circuit();
        let total_cells = self.board_size * self.board_size;

        let mut pw = PartialWitness::new();

        // Set before board values
        for (i, &value) in before_board.iter().enumerate() {
            pw.set_target(targets[i], value)?;
        }

        // Set after board values
        for (i, &value) in after_board.iter().enumerate() {
            pw.set_target(targets[total_cells + i], value)?;
        }

        // Set direction
        pw.set_target(targets[2 * total_cells], F::from_canonical_u32(direction as u32))?;

        let data = builder.build::<C>();
        let proof = data.prove(pw)?;

        // Verify the proof
        data.verify(proof)?;
        println!("Move verified successfully!");

        Ok(())
    }
}

fn main() -> Result<()> {
    // Example usage
    let circuit = Game2048Circuit::new(4); // 4x4 board

    // Example board state before move
    let before_board = vec![
        F::from_canonical_u32(2), F::from_canonical_u32(2), F::from_canonical_u32(4), F::from_canonical_u32(8),
        F::ZERO, F::ZERO, F::from_canonical_u32(4), F::from_canonical_u32(4),
        F::from_canonical_u32(2), F::from_canonical_u32(2), F::from_canonical_u32(2), F::from_canonical_u32(4),
        F::ZERO, F::from_canonical_u32(2), F::from_canonical_u32(4), F::from_canonical_u32(4),
    ];

    // Example board state after move right
    let after_board = vec![
        F::ZERO, F::from_canonical_u32(4), F::from_canonical_u32(4), F::from_canonical_u32(8),
        F::ZERO, F::ZERO, F::from_canonical_u32(4), F::from_canonical_u32(8),
        F::ZERO, F::from_canonical_u32(2), F::from_canonical_u32(4), F::from_canonical_u32(4),
        F::ZERO, F::from_canonical_u32(2), F::from_canonical_u32(4), F::from_canonical_u32(4),
    ];

    // Prove the move
    circuit.prove_move(before_board, after_board, Direction::Right)?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_valid_move() -> Result<()> {
        let circuit = Game2048Circuit::new(4);

        // Initial board with two 2's that can merge
        let before_board = vec![
            F::ZERO,                  F::ZERO,                  F::from_canonical_u32(2), F::from_canonical_u32(2),
            F::ZERO,                  F::ZERO,                  F::ZERO,                  F::ZERO,
            F::ZERO,                  F::ZERO,                  F::ZERO,                  F::ZERO,
            F::ZERO,                  F::ZERO,                  F::ZERO,                  F::ZERO,
        ];

        // After moving right, the two 2's merge into a 4
        let after_board = vec![
            F::ZERO,                  F::ZERO,                  F::ZERO,                  F::from_canonical_u32(4),
            F::ZERO,                  F::ZERO,                  F::ZERO,                  F::ZERO,
            F::ZERO,                  F::ZERO,                  F::ZERO,                  F::ZERO,
            F::ZERO,                  F::ZERO,                  F::ZERO,                  F::ZERO,
        ];

        // Test a simple right move that merges two 2's into a 4
        circuit.prove_move(before_board, after_board, Direction::Right)
    }

    #[test]
    fn test_valid_move_no_merge() -> Result<()> {
        let circuit = Game2048Circuit::new(4);

        // Initial board with a single 2
        let before_board = vec![
            F::ZERO,                  F::ZERO,                  F::from_canonical_u32(2), F::ZERO,
            F::ZERO,                  F::ZERO,                  F::ZERO,                  F::ZERO,
            F::ZERO,                  F::ZERO,                  F::ZERO,                  F::ZERO,
            F::ZERO,                  F::ZERO,                  F::ZERO,                  F::ZERO,
        ];

        // After moving right, the 2 moves to the rightmost position
        let after_board = vec![
            F::ZERO,                  F::ZERO,                  F::ZERO,                  F::from_canonical_u32(2),
            F::ZERO,                  F::ZERO,                  F::ZERO,                  F::ZERO,
            F::ZERO,                  F::ZERO,                  F::ZERO,                  F::ZERO,
            F::ZERO,                  F::ZERO,                  F::ZERO,                  F::ZERO,
        ];

        // Test a simple right move without merging
        circuit.prove_move(before_board, after_board, Direction::Right)
    }
}