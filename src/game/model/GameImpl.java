package game.model;
import game.control.Player;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

/**
 * Implementation of the Dots and Boxes Game object implementing the interface.
 * Stores two players and Board object.
 */
public class GameImpl implements Game {

    //@ private invariant players.length == 2;
    //@ private invariant 0 <= currentPlayer && currentPlayer < players.length;
    //@ private invariant board != null;

    /**
     * Holding the array of the players.
     */
    private final Player[] players;


    /**
     * Field for holding the index of the current player.
     */
    private int currentPlayer;

    /**
     * Holding the Board of the game
     */
    private Board board;

    /**
     * Constructor for a Game instance with the given players to play.
     *
     * @param p1 first player.
     * @param p2 second player.
     */
    public GameImpl(Player p1, Player p2) {
        this.players = new Player[2];
        this.players[0] = p1;
        this.players[1] = p2;
        currentPlayer = 0;
        this.board = new Board();
    }

    /**
     * returns the board object for the specific game
     *
     * @return the board for the game
     */
    //@ ensures \result == board;
    public Board getBoard() {
        return board;
    }

    /**
     * The method which checks whether the move completes the square meaning that there is no need to change turn.
     *
     * @param move move to check.
     * @return true if move completes square, otherwise false.
     */
    //@ ensures \result == (board.completeSquare(move) > -1);
    public boolean completesSquare(int move) {
        return board.completeSquare(move) > -1;
    }

    /**
     * Checks if the game is over.
     *
     * @return true if the game is over, otherwise false
     */
    //@ ensures \result == board.isFull();
    //@ pure
    @Override
    public boolean isGameOver() {
        return this.board.isFull();
    }

    /**
     * Gets the player whose turn it is.
     *
     * @return the player whose turn it is
     */
    //@ ensures \result == players[currentPlayer];
    @Override
    public Player getTurn() {
        return this.players[this.currentPlayer];
    }

    /**
     * Gets the winner of the game.
     *
     * @return the winner player if the game is over, otherwise null
     */
    //@ ensures \result == (isGameOver() ? (board.isWinner(players[0].getMark()) ? players[0] : players[1]) : null);
    @Override
    public Player getWinner() {
        if (!isGameOver()) {
            return null;
        } else if (board.isWinner(players[0].getMark())) return players[0];
        else return players[1];
    }

    /**
     * Gets a list of valid moves for the current game state.
     *
     * @return a list of valid moves
     */
    //@ ensures \result != null && (\forall int i; 0 <= i && i < Board.INDEX; board.isEmptyField(i) ==> (\exists Move m; \result.contains(m) && m.getIndex() == i));
    @Override
    public List<Move> getValidMoves() {
        List<Move> moves = new ArrayList<>();
        for (int i = 0; i < Board.INDEX; i++) {
            if (board.isEmptyField(i)) {
                moves.add(new MoveGame(i, getTurn().getMark()));
            }
        }
        return moves;
    }

    /**
     * Checks if a given move is valid for the current game state.
     *
     * @param move the move to check
     * @return true if the move is valid, otherwise false
     */
    //@ ensures \result == (move != null && board.isEmptyField(move.getIndex()));
    @Override
    public boolean isValidMove(Move move) {
        if (Objects.isNull(move)) {
            return false;
        } else {
            return board.isEmptyField(move.getIndex());
        }
    }

    /**
     * Executes a move in the game.
     *
     * @param move the move to be executed
     */
    //@ ensures board.getField(move.getIndex()) == move.getMark();
    @Override
    public void doMove(Move move) {
        if (move.getIndex() >= 0 && move.getIndex() < Board.INDEX) {
            board.setField(move.getIndex(), move.getMark());
        }
    }

    /**
     * Restarts the game by resetting the board and setting the current player to player 1.
     */
    //@ ensures (\forall int i; 0 <= i && i < Board.INDEX; board.isEmptyField(i));
    @Override
    public void restart() {
        this.board.reset();
        currentPlayer = 0;
    }

    /**
     * Changes the turn to the other player.
     */
    //@ ensures currentPlayer == (\old(currentPlayer) == 0 ? 1 : 0);
    @Override
    public void changeTurn() {
        if (currentPlayer == 0) currentPlayer = 1;
        else currentPlayer = 0;
    }

    /**
     * Sets the game's board based on a deep copy of another board.
     *
     * @param board the board to copy
     */
    //@ ensures this.board.equals(board.deepCopy());
    public void setCopyBoard(Board board) {
        this.board = board.deepCopy();
    }
}
