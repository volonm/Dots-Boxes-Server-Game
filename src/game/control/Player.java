package game.control;

import game.model.Mark;
import game.model.Game;
import game.model.Move;

/**
 * Interface for the Player instance.
 */
public interface Player {

    /**
     * Returns the name of the Player.
     *
     * @return name of the player.
     */
    //@ pure;
    String getName();

    /**
     * Determines the move of the Player and returns it.
     *
     * @return move of the player.
     */
    //@requires game != null;
    //@ensures (!game.isGameOver() && !game.getValidMoves().isEmpty()) ==> game.getValidMoves().contains(\result);
    Move determineMove(Game game);

    /**
    * Returns the mark of the Player.
    *
    * @return name of the player.
    */
    //@ pure;
    Mark getMark();

    /**
     * Returns the in game string representation of the Player, namely string of format
     * Player + name of the player or strategy.
     *
     * @return in game Player string representation.
     */
    //@pure;
    String toString();


}
