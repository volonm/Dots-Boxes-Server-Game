package game.model;

/**
 * An interface for the move in a turn-based game. The move will handle the index
 * on which it should be placed and the mark.
 */
public interface Move {

    /**
     * Returns the Mark of the enum type of the Move.
     *
     * @return - mark of the move.
     */
    //@ pure;
    Mark getMark();

    /**
     * Returns the index of the move in the game. The index of the move should be 0 < DIM*DIM,
     * where DIM is a dimension of the Game's Board.
     *
     * @return - index of the move.
     */
    //@pure;
    int getIndex();
}
