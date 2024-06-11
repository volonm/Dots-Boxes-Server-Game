package game.model;

/**
 * Represents a mark in the Dots And Boxes Game. There are three possible values:
 * Mark RED, Mark BLUE and Mark.EMPTY.
 */
public enum Mark {
    EMPTY, RED, BLUE;

    /**
     * Returns the other Mark, if the mark was EMPTY then returns EMPTY.
     *
     * @return the other mark is this mark is not EMPTY or EMPTY
     */
    //@ensures this == RED ==> \result == BLUE && this == BLUE ==> \result == RED && this == EMPTY ==> \result == EMPTY;
    public Mark other() {
        if (this == RED) {
            return BLUE;
        } else if (this == BLUE) {
            return RED;
        } else {
            return EMPTY;
        }
    }
}
