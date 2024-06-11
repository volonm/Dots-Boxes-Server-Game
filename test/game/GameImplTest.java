package game;

import game.control.HumanPlayer;
import game.control.Player;
import game.control.ai.ComputerPlayer;
import game.control.ai.SmartStrategy;
import game.model.Board;
import game.model.GameImpl;
import game.model.Mark;
import game.model.MoveGame;
import game.model.Move;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.Random;

import static org.junit.jupiter.api.Assertions.*;

class GameImplTest {

    private Player player1;
    private Player player2;
    private GameImpl game;

    /**
     * Set up before each test.
     */
    @BeforeEach
    void setUp() {
        player1 = new HumanPlayer("Player 1", Mark.BLUE);
        player2 = new ComputerPlayer(new SmartStrategy(), Mark.RED);
        game = new GameImpl(player1, player2);
    }


    /**
     * Test to check the initial state of the board and game conditions.
     */
    @Test
    void testInitialSetup() {
        assertFalse(game.isGameOver());
        assertEquals(player1, game.getTurn());
        assertNull(game.getWinner());
        assertEquals(Board.INDEX, game.getValidMoves().size());
        for (int i = 0; i < Board.INDEX; i++) {
            assertTrue(game.isValidMove(new MoveGame(i, player1.getMark())));
        }
    }

    /**
     * test that the computer will avoid giving the other player a free square
     */
    @Test
    void testComputerHelpAvoidance() {
        game.doMove(new MoveGame(0, Mark.BLUE));
        game.doMove(new MoveGame(1, Mark.BLUE));
        game.doMove(new MoveGame(2, Mark.BLUE));
        game.doMove(new MoveGame(3, Mark.BLUE));
        game.doMove(new MoveGame(4, Mark.BLUE));
        game.doMove(new MoveGame(11, Mark.BLUE));
        game.doMove(new MoveGame(12, Mark.BLUE));
        game.doMove(new MoveGame(13, Mark.BLUE));
        game.doMove(new MoveGame(14, Mark.BLUE));
        game.doMove(new MoveGame(15, Mark.BLUE));
        game.doMove(new MoveGame(22, Mark.BLUE));
        game.doMove(new MoveGame(23, Mark.BLUE));
        game.doMove(new MoveGame(24, Mark.BLUE));
        game.doMove(new MoveGame(25, Mark.BLUE));
        game.doMove(new MoveGame(26, Mark.BLUE));
        game.doMove(new MoveGame(33, Mark.BLUE));
        game.doMove(new MoveGame(34, Mark.BLUE));
        game.doMove(new MoveGame(35, Mark.BLUE));
        game.doMove(new MoveGame(36, Mark.BLUE));
        game.doMove(new MoveGame(37, Mark.BLUE));
        game.doMove(new MoveGame(44, Mark.BLUE));
        game.doMove(new MoveGame(45, Mark.BLUE));
        game.doMove(new MoveGame(46, Mark.BLUE));
        game.doMove(new MoveGame(47, Mark.BLUE));
        game.doMove(new MoveGame(48, Mark.BLUE));
        game.doMove(new MoveGame(55, Mark.BLUE));
        game.doMove(new MoveGame(56, Mark.BLUE));
        game.doMove(new MoveGame(57, Mark.BLUE));
        game.doMove(new MoveGame(58, Mark.BLUE));

        int move = player2.determineMove(game).getIndex();
        assertTrue(move == 59 || move == 54);
    }

    /**
     * tests if the computer takes a square if it can
     */
    @Test
    void testComputerSquare() {
        game.doMove(new MoveGame(0, Mark.BLUE));
        game.doMove(new MoveGame(11, Mark.BLUE));
        game.doMove(new MoveGame(5, Mark.BLUE));
        assertEquals(6, player2.determineMove(game).getIndex());
    }

    /**
     * tests if the computer takes the square that can chain him more
     */
    @Test
    void testComputerDoubleSquare() {
        game.doMove(new MoveGame(0, Mark.BLUE));
        game.doMove(new MoveGame(11, Mark.BLUE));
        game.doMove(new MoveGame(5, Mark.BLUE));
        game.doMove(new MoveGame(1, Mark.BLUE));
        game.doMove(new MoveGame(7, Mark.BLUE));
        game.doMove(new MoveGame(4, Mark.BLUE));
        game.doMove(new MoveGame(10, Mark.BLUE));
        game.doMove(new MoveGame(15, Mark.BLUE));
        assertEquals(6, player2.determineMove(game).getIndex());
    }

    /**
     * Test on doing the move and how it is removed form the valid moves.
     */
    @Test
    void testValidMove() {
        Move move = game.getValidMoves().get(0);
        assertTrue(game.isValidMove(move));
        game.doMove(move);
        assertFalse(game.getValidMoves().contains(move));
        for (int i = 1; i < Board.INDEX; i++) {
            Move m = new MoveGame(i, player1.getMark());
            assertTrue(game.isValidMove(m));
            game.doMove(m);
            assertFalse(game.isValidMove(m));
            Move previousMove = new MoveGame(i - 1, player1.getMark());
            assertFalse(game.isValidMove(previousMove));
        }
    }

    /**
     * Test on the move that is invalid and test whether doing tha invalid move throws an error.
     */
    @Test
    void testInvalidMove() {
        Move invalidMove = new MoveGame(-1, Mark.BLUE);
        assertFalse(game.isValidMove(invalidMove));
        assertFalse(game.getValidMoves().contains(invalidMove));
        game.doMove(invalidMove);
        game.doMove(invalidMove);
        //Test whether the game still can continue.
        Move validMove = new MoveGame(0, Mark.BLUE);
        assertTrue(game.isValidMove(validMove));
        game.doMove(validMove);
        assertFalse(game.isValidMove(validMove));
        assertFalse(game.isValidMove(validMove));
    }

    /**
     * Test on the isGameover() method.
     */
    @Test
    void testGameOver() {
        assertFalse(game.isGameOver());

        // Fill the board to make the game over
        for (Move move : game.getValidMoves()) {
            game.doMove(move);
        }

        assertTrue(game.isGameOver());
        assertNotNull(game.getWinner());
    }

    /**
     * Test on the restart method
     */
    @Test
    void testRestart() {
        assertFalse(game.isGameOver());

        // Make some moves
        for (int i = 0; i < 4; i++) {
            game.doMove(game.getValidMoves().get(i));
        }

        game.restart();

        // After restart, the board should be empty, and the turn should be back to player1
        assertFalse(game.isGameOver());
        assertEquals(player1, game.getTurn());
        assertNull(game.getWinner());
        assertEquals(60, game.getValidMoves().size());
        for (int i = 0; i < Board.INDEX; i++) {
            game.doMove(new MoveGame(i, Mark.BLUE));
        }
        assertTrue(game.isGameOver());
        assertNotNull(game.getWinner());
        game.restart();
        for (int i = 0; i < Board.INDEX; i++) {
            assertFalse(game.isGameOver());
            assertNull(game.getWinner());
            assertTrue(game.isValidMove(new MoveGame(i, Mark.BLUE)));
        }
    }

    /**
     * Test on Changing the player's turns
     */
    @Test
    void testChangeTurn() {
        Player p1 = game.getTurn();
        game.changeTurn();
        assertNotNull(p1);

        Player p2 = game.getTurn();
        assertNotNull(p2);
        assertNotEquals(p1, p2);
        game.changeTurn();

        Player p1AfterChange = game.getTurn();
        assertNotNull(p1AfterChange);

        assertEquals(p1, p1AfterChange);
        game.changeTurn();

        Player p2AfterChange = game.getTurn();
        assertEquals(p2, p2AfterChange);
        assertNotNull(p2AfterChange);
    }

    /**
     * Test on playing the full game with random moves for the players.
     */
    @Test
    void testPlayFullRandomGame() {
        while (!game.isGameOver()) {
            Move randomMove = game.getValidMoves().get(new Random().nextInt(game.getValidMoves().size()));
            int moves = game.getValidMoves().size();
            game.doMove(randomMove);
            if (!game.completesSquare(randomMove.getIndex())) {
                game.changeTurn();
            }
            assertTrue(moves > game.getValidMoves().size());

        }
        assertTrue(game.isGameOver());
        assertTrue(game.getValidMoves().isEmpty());
        assertTrue(game.getWinner().equals(player1) || game.getWinner().equals(player2));
        assertFalse(game.getWinner().equals(player1) && game.getWinner().equals(player2));
    }


    /**
     * Test on playing the full game with a predefined test case.
     */
    @Test
    void testPlayFullTestCase() {
        // Define the moves to do. Just a test-case all moves in game in indexes.
        int[] moves = new int[]{3, 5, 8, 16, 25, 27, 38, 49, 50, 6, 39, 17, 28, 7, 18, 29,
                40, 51, 19, 30, 41, 52, 31, 36, 53, 54, 10, 32, 4, 48, 59, 47, 58, 42, 15, 9,
                20, 21, 14, 37, 57, 46, 35, 24, 2, 13, 0, 11, 22, 33, 55, 44, 56, 45, 34, 23, 12, 1, 26, 43};

        for (int move : moves) {
            MoveGame moveToPlay = new MoveGame(move, game.getTurn().getMark());
            game.doMove(moveToPlay);
            if (!game.completesSquare(moveToPlay.getIndex())) game.changeTurn();
        }

        //test whether the game is fully finished an all the endpoints
        assertTrue(game.isGameOver());
        assertTrue(game.getValidMoves().isEmpty());

        //test that winner exists and it is only one player
        assertTrue(game.getWinner().equals(player1) || game.getWinner().equals(player2));
        assertFalse(game.getWinner().equals(player1) && game.getWinner().equals(player2));
        assertEquals(player2, game.getWinner());
    }

}
