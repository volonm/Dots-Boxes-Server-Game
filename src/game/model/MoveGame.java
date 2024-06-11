package game.model;

/**
 * The Move implementation in a Dots and Boxes game. The move will handle the index
 * on which it should be placed and the mark.
 */
public class MoveGame implements Move {

    /**
     * The index int field for the Move.
     */
    private final int index;

    /**
     * The mark field to store mark of the Move.
     */
    private final Mark mark;

    /**
     * The constructor to create the move with the given index and mark. The index of the move should be 0 < DIM*DIM,
     * where DIM is a dimension of the Game's Board.
     *
     * @param index index of the Move.
     * @param mark  mark of the Move.
     */
    //@ requires index >= 0 && index < (Board.DIM * Board.DIM) && mark != Mark.EMPTY;
    public MoveGame(int index, Mark mark) {
        this.index = index;
        this.mark = mark;
    }

    /**
     * returns the mark of the move
     *
     * @return the mark of the move
     */
    @Override
    public Mark getMark() {
        return this.mark;
    }

    /**
     * gets the index of the move
     *
     * @return the index of the move
     */
    @Override
    public int getIndex() {
        return this.index;
    }
}
