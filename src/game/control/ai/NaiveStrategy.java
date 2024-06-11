package game.control.ai;

import game.model.Game;
import game.model.Move;

import java.util.List;
import java.util.Random;

/**
 * Naive Strategy Implementation which determines the move for the Computer Player.
 * The naive strategy just returns the random valid playable move.
 */

public class NaiveStrategy implements Strategy {

    /**
     * returns the name of the naive strategy
     *
     * @return the name of the naive strategy
     */
    @Override
    public String getName() {
        return "Naive Strategy";
    }

    /**
     * The Naive strategy determines the move for the Computer player. For naive representation,
     * the determined move returns the random valid move.
     *
     * @param game - current game situation
     * @return move to play.
     */
    @Override
    public Move determineMove(Game game) {
        List<Move> validMoves = game.getValidMoves();
        return validMoves.get(new Random().nextInt(validMoves.size()));
    }
}
