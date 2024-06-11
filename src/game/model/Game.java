package game.model;

import java.util.List;

import game.control.Player;

/**
 * A turn-based game interface.
 */
public interface Game {
    //@ instance invariant !isGameOver() ==> getValidMoves().size() > 0;
    //@ instance invariant !isGameOver() ==> getWinner() == null;
    //@ instance invariant !isGameOver() ==> getTurn() != null;


    /**
     * Check if the game is over, checks the game has finished meaning
     * that there are no valid moves left for players to play. Returns true if the game is over, otherwise - false.
     *
     * @return whether the game is over
     */
    //@ pure;
    boolean isGameOver();

    /**
     * Query whose turn it is
     *
     * @return the player whose turn it is
     */
    //@ pure;
    Player getTurn();

    /**
     * Get the winner of the game. If the game is a draw, then this method returns null.
     *
     * @return the winner, or null if no player is the winner or the game is not over
     */
    //@ pure;
    Player getWinner();

    /**
     * Return all moves that are valid in the current state of the game for the current player.
     *
     * @return the list of currently valid moves for the current player.
     */
    //@ ensures (\forall Move m; \result.contains(m); isValidMove(m));
    //@ pure;
    List<Move> getValidMoves();

    /**
     * Check if a move is a valid move for the current player.
     *
     * @param move the move to check for the current player.
     * @return true if the move is a valid move for the current player.
     */
    //@ ensures \result <==> (\exists Move m; getValidMoves().contains(m); m.equals(move));
    //@ pure;
    boolean isValidMove(Move move);

    /**
     * Perform the move, assuming it is a valid move.
     *
     * @param move the move to play
     */
    //@ requires isValidMove(move);
    void doMove(Move move);

    /**
     * Performs a restart of the game in case user's want to play one more round.
     */
    void restart();

    /**
     * Changes the current player to the other.
     */
    void changeTurn();
}

