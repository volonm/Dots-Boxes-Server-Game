package game.control.ai;

import game.control.HumanPlayer;
import game.model.Game;
import game.model.GameImpl;
import game.model.Mark;
import game.model.Move;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;

/**
 * A smart strategy for making moves in a game.
 */
public class SmartStrategy implements Strategy {

    /**
     * Returns the name of the strategy.
     *
     * @return the name of the strategy
     */
    @Override
    public String getName() {
        return "Smart strategy";
    }

    /**
     * Calculates the current move according to the strategy, and its mark, and returns the Move.
     * Returns null if the game has ended or the board is full.
     *
     * @param game - the current game situation
     * @return a Move to play
     */
    @Override
    public Move determineMove(Game game) {
        List<Move> bestMoves = findMovesCompletingSquare(game.getValidMoves(), (GameImpl) game);

        if (!bestMoves.isEmpty()) {
            return getRandomMove(bestMoves);
        }

        List<Move> newValidMoves = filterMovesAvoidingOpponentSquare(game.getValidMoves(), (GameImpl) game);

        if (!newValidMoves.isEmpty()) {
            return getRandomMove(newValidMoves);
        }

        // If neither completing a square nor avoiding helping the opponent is possible, choose a random move
        return getRandomMove(game.getValidMoves());
    }

    /**
     * Finds moves that complete a square and don't help the opponent complete a square.
     *
     * @param validMoves - a list of valid moves
     * @param currentGame - the current state of the game
     * @return a list of moves completing a square
     */
    private List<Move> findMovesCompletingSquare(List<Move> validMoves, GameImpl currentGame) {
        List<Move> bestMoves = new ArrayList<>();
        for (Move move : validMoves) {
            GameImpl hypotheticalGame = createHypotheticalGame(currentGame);
            hypotheticalGame.doMove(move);

            if (hypotheticalGame.completesSquare(move.getIndex())) {
                if (givesSecondSquareCompletion(hypotheticalGame)) {
                    return List.of(move);
                }
                bestMoves.add(move);
            }
        }
        return bestMoves;
    }

    /**
     * Checks if making a move gives the player a second square completion in the hypothetical game state.
     *
     * @param hypotheticalGame the hypothetical game state after the current move
     * @return true if giving a second square completion, false otherwise
     */
    private boolean givesSecondSquareCompletion(GameImpl hypotheticalGame) {
        for (Move secondMove : hypotheticalGame.getValidMoves()) {
            GameImpl hypotheticalGame2 = createHypotheticalGame(hypotheticalGame);
            hypotheticalGame2.doMove(secondMove);
            if (hypotheticalGame2.completesSquare(secondMove.getIndex())){
                return true;
            }
        } return false;
    }

    /**
     * Filters moves to avoid helping the opponent complete a square.
     *
     * @param validMoves  a list of valid moves
     * @param currentGame the current state of the game
     * @return a filtered list of moves avoiding helping the opponent complete a square
     */
    private List<Move> filterMovesAvoidingOpponentSquare(List<Move> validMoves, GameImpl currentGame) {
        List<Move> newValidMoves = new ArrayList<>(validMoves);

        for (Move move : validMoves) {
            GameImpl hypotheticalGame = createHypotheticalGame(currentGame);
            hypotheticalGame.doMove(move);
            hypotheticalGame.changeTurn();

            List<Move> validOpponentMoves = hypotheticalGame.getValidMoves();
            for (Move secondMove : validOpponentMoves){
                GameImpl hypotheticalGame2 = createHypotheticalGame(hypotheticalGame);
                hypotheticalGame2.doMove(secondMove);
                if (hypotheticalGame2.completesSquare(secondMove.getIndex())) {
                    newValidMoves.remove(move);
                }
            }
        }
        return newValidMoves;
    }

    /**
     * Creates a hypothetical game state based on the current game state.
     *
     * @param currentGame the current state of the game
     * @return a new GameImpl instance representing a hypothetical game state
     */
    private GameImpl createHypotheticalGame(GameImpl currentGame) {
        GameImpl hypotheticalGame = new GameImpl(new HumanPlayer("P1", Mark.BLUE), new HumanPlayer("P2", Mark.RED));
        hypotheticalGame.setCopyBoard(currentGame.getBoard());
        return hypotheticalGame;
    }

    /**
     * Returns a random move from the given list of moves.
     *
     * @param moves a list of moves
     * @return a randomly selected Move from the list
     */
    private Move getRandomMove(List<Move> moves) {
        return moves.get(new Random().nextInt(moves.size()));
    }
}
