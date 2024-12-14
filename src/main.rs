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
                
                // Basic cell transition constraints
                let stays_same = builder.is_equal(current, current_after);
                let becomes_zero = builder.is_equal(current_after, zero_target);

                // For each cell, we need to check if it can merge with neighbors
                let mut can_merge = Vec::new();
                
                // Check up
                if row > 0 {
                    let up_idx = (row - 1) * self.board_size + col;
                    let up_val = before_board[up_idx];
                    let up_after = after_board[up_idx];
                    let values_equal = builder.is_equal(current, up_val);
                    let merged_value = builder.mul_const(F::TWO, current);
                    let merged_correctly = builder.is_equal(up_after, merged_value);
                    let merge_happened = builder.and(values_equal, merged_correctly);
                    can_merge.push(builder.and(merge_happened, is_up));
                }

                // Check down
                if row < self.board_size - 1 {
                    let down_idx = (row + 1) * self.board_size + col;
                    let down_val = before_board[down_idx];
                    let down_after = after_board[down_idx];
                    let values_equal = builder.is_equal(current, down_val);
                    let merged_value = builder.mul_const(F::TWO, current);
                    let merged_correctly = builder.is_equal(down_after, merged_value);
                    let merge_happened = builder.and(values_equal, merged_correctly);
                    can_merge.push(builder.and(merge_happened, is_down));
                }

                // Check left
                if col > 0 {
                    let left_idx = row * self.board_size + (col - 1);
                    let left_val = before_board[left_idx];
                    let left_after = after_board[left_idx];
                    let values_equal = builder.is_equal(current, left_val);
                    let merged_value = builder.mul_const(F::TWO, current);
                    let merged_correctly = builder.is_equal(left_after, merged_value);
                    let merge_happened = builder.and(values_equal, merged_correctly);
                    can_merge.push(builder.and(merge_happened, is_left));
                }

                // Check right
                if col < self.board_size - 1 {
                    let right_idx = row * self.board_size + (col + 1);
                    let right_val = before_board[right_idx];
                    let right_after = after_board[right_idx];
                    let values_equal = builder.is_equal(current, right_val);
                    let merged_value = builder.mul_const(F::TWO, current);
                    let merged_correctly = builder.is_equal(right_after, merged_value);
                    let merge_happened = builder.and(values_equal, merged_correctly);
                    can_merge.push(builder.and(merge_happened, is_right));
                }

                // A cell must either:
                // 1. Stay the same (if no movement possible in chosen direction)
                // 2. Become zero (if moved or merged)
                // 3. Double in value (if merged with equal value)
                let any_merge_possible = if can_merge.is_empty() {
                    zero_target
                } else {
                    // Convert boolean targets to field targets first
                    let merge_targets: Vec<_> = can_merge.iter()
                        .map(|&b| builder.select(b, one_target, zero_target))
                        .collect();
                    
                    // Then sum them up
                    let merge_sum = builder.add_many(&merge_targets);
                    
                    // Finally check if exactly one merge happened
                    let is_one_merge = builder.is_equal(merge_sum, one_target);
                    builder.select(is_one_merge, one_target, zero_target)
                };

                // The cell's final state must be valid
                let stays_same_target = builder.select(stays_same, one_target, zero_target);
                let becomes_zero_target = builder.select(becomes_zero, one_target, zero_target);
                
                let valid_state = [
                    stays_same_target,
                    becomes_zero_target,
                    any_merge_possible,
                ];
                let state_sum = builder.add_many(&valid_state);
                builder.connect(state_sum, one_target);
            }
        }

        // Verify that exactly one direction is chosen
        let up_target = builder.select(is_up, one_target, zero_target);
        let down_target = builder.select(is_down, one_target, zero_target);
        let left_target = builder.select(is_left, one_target, zero_target);
        let right_target = builder.select(is_right, one_target, zero_target);
        
        let direction_targets = [up_target, down_target, left_target, right_target];
        let sum = builder.add_many(&direction_targets);
        builder.connect(sum, one_target);
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

        let before_board = vec![
            F::from_canonical_u32(2), F::from_canonical_u32(2), F::ZERO, F::ZERO,
            F::ZERO, F::from_canonical_u32(4), F::ZERO, F::ZERO,
            F::ZERO, F::ZERO, F::from_canonical_u32(4), F::ZERO,
            F::ZERO, F::ZERO, F::ZERO, F::from_canonical_u32(2),
        ];

        let after_board = vec![
            F::ZERO, F::ZERO, F::ZERO, F::from_canonical_u32(4),
            F::ZERO, F::ZERO, F::ZERO, F::from_canonical_u32(4),
            F::ZERO, F::ZERO, F::ZERO, F::from_canonical_u32(4),
            F::ZERO, F::ZERO, F::ZERO, F::from_canonical_u32(2),
        ];

        circuit.prove_move(before_board, after_board, Direction::Right)
    }
}