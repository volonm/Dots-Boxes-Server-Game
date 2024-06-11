package game.control.ai;

import game.model.Game;
import game.model.Move;

/**
 * Interface for the Strategy for playing the Dots and Boxes.
 */
public interface Strategy {

    /**
     * Returns the name of the strategy.
     *
     * @return name of the strategy
     */
    /*@ensures \result != null;
        @pure;
    */
    String getName();

    /**
     * Calculates the current move according to
     * the strategy, and it's mark and returns the Move.
     * Null in case the game ended or the board is full
     *
     * @param game - current game situation
     * @return a Move to play
     */
    /*@requires game != null;
    @ensures (!game.isGameOver() && !game.getValidMoves().isEmpty()) ==> game.getValidMoves().contains(\result);*/
    Move determineMove(Game game);
}
