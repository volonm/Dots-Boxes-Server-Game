package game;

import game.model.Board;
import game.model.Mark;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.BeforeEach;

import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Test of the Board class implementation.
 */
class BoardTest {
    /**
     * Board object to test
     */
    private Board board;

    /**
     * Before each test initialize the Board object.
     */
    @BeforeEach
    public void setUp() {
        board = new Board();
    }

    /**
     * Test of the Initial state of the board. When Board object is initialized all the filed has to be Empty.
     */
    @Test
    void testInitialization() {
        for (int i = 0; i < Board.INDEX; i++) {
            assertEquals(Mark.EMPTY, board.getField(i));
        }
    }

    /**
     * Test of isField method, which returns true if the method is true if the index is valid.
     */
    @Test
    void testIsFieldIndex() {
        int maxIndex = Board.INDEX - 1;
        assertFalse(board.isField(-1));
        assertTrue(board.isField(0));
        assertTrue(board.isField(maxIndex));
        assertTrue(board.isField(30));
        assertFalse(board.isField(maxIndex + 1));
        assertFalse(board.isField(maxIndex * 2));
    }

    /**
     * Test on methods setField() and getField(), setting the fields and getting it.
     */
    @Test
    void testSetAndGetFieldIndex() {
        board.setField(0, Mark.BLUE);
        assertEquals(Mark.BLUE, board.getField(0));
        assertEquals(Mark.EMPTY, board.getField(1));
        board.setField(56, Mark.RED);
        assertEquals(Mark.RED, board.getField(56));
        // The field isn't supposed to change if set already.
        board.setField(56, Mark.BLUE);
        assertEquals(Mark.RED, board.getField(56));
    }

    /**
     * Test of SetField() and getPoints() methods with setting the squares and checking the points.
     */
    @Test
    void testSetFieldSquares() {
        for (int i = 0; i < Board.INDEX; i++) {
            assertTrue(board.isEmptyField(i));
        }
        board.setField(0, Mark.RED);
        board.setField(5, Mark.RED);
        board.setField(6, Mark.RED);
        board.setField(16, Mark.RED);
        board.setField(17, Mark.RED);
        board.setField(22, Mark.RED);
        assertEquals(Mark.RED, board.getField(0));
        assertEquals(Mark.RED, board.getField(5));
        assertEquals(Mark.RED, board.getField(6));
        assertEquals(Mark.RED, board.getField(16));
        assertEquals(Mark.RED, board.getField(17));
        assertEquals(Mark.RED, board.getField(22));

        // Calculating points
        assertEquals(0, board.getPoints(Mark.RED));
        board.setField(11, Mark.BLUE);
        assertEquals(2, board.getPoints(Mark.BLUE));
    }


    /**
     * Test of isEmptyField() method, which returns true if the method is true if the index is valid.
     */
    @Test
    void testIsEmptyField() {
        for (int i = 0; i < Board.INDEX; i++) {
            assertTrue(board.isEmptyField(i));
        }
        board.setField(0, Mark.RED);
        board.setField(5, Mark.RED);
        board.setField(6, Mark.RED);
        board.setField(16, Mark.RED);
        board.setField(17, Mark.RED);
        board.setField(22, Mark.RED);
        board.setField(11, Mark.RED);
        assertFalse(board.isEmptyField(0));
        assertFalse(board.isEmptyField(5));
        assertFalse(board.isEmptyField(6));
        assertFalse(board.isEmptyField(16));
        assertFalse(board.isEmptyField(17));
        assertFalse(board.isEmptyField(22));
        assertFalse(board.isEmptyField(11));
        //Test with invalid index.
        assertFalse(board.isEmptyField(1151515152));
    }


    /**
     * Test of the deepCopy() method which creates the deep copy of the current board.
     */
    @Test
    void testDeepCopy() {
        /* Setting some board fields */
        board.setField(0, Mark.BLUE);
        board.setField(1, Mark.BLUE);
        board.setField(5, Mark.RED);
        board.setField(11, Mark.BLUE);
        board.setField(7, Mark.BLUE);
        board.setField(17, Mark.BLUE);
        board.setField(16, Mark.BLUE);
        board.setField(22, Mark.RED);
        board.setField(6, Mark.RED);
        /* Creating a board deep copy */
        Board boardCopy = board.deepCopy();
        /* Testing the set fields with painted squares */
        assertEquals(Mark.BLUE, boardCopy.getField(0));
        assertEquals(Mark.BLUE, boardCopy.getField(1));
        assertEquals(Mark.BLUE, boardCopy.getField(16));
        assertEquals(Mark.BLUE, boardCopy.getField(17));
        assertNotEquals(Mark.BLUE, boardCopy.getField(3));
        assertEquals(Mark.EMPTY, boardCopy.getField(20));
        assertEquals(Mark.RED, boardCopy.getField(5));
        assertEquals(Mark.RED, boardCopy.getField(6));
        assertEquals(Mark.RED, boardCopy.getField(22));

    }


    /**
     * Test of the reset() method.
     */
    @Test
    void testReset() {
        board.setField(0, Mark.RED);
        board.setField(Board.INDEX - 1, Mark.BLUE);
        board.reset();
        assertEquals(Mark.EMPTY, board.getField(0));
        assertEquals(Mark.EMPTY, board.getField(Board.INDEX - 1));
    }


    /**
     * Test on the isFull() method.
     */
    @Test
    void testIsFull() {
        for (int i = 0; i < Board.INDEX - 1; i++) {
            board.setField(i, Mark.RED);
        }
        assertFalse(board.isFull());

        board.setField((Board.INDEX - 1), Mark.BLUE);
        assertTrue(board.isFull());
    }

    /**
     * Test of the completeSquare() method.
     */
    @Test
    void testCompleteSquare() {
        /*
         * -12  -top
         * |17  -left
         * 18|  -right
         * _23  -bottom
         */
        board.setField(18, Mark.RED);
        board.setField(17, Mark.RED);
        board.setField(23, Mark.RED);
        board.setField(12, Mark.RED);

        assertEquals(17, board.completeSquare(12));
        assertEquals(17, board.completeSquare(18));
        assertEquals(17, board.completeSquare(23));
        assertEquals(17, board.completeSquare(17));

        /*
         *  -13   -top
         *  |18   -left
         *  19|   -right
         * _25    -bottom
         */
        board.setField(13, Mark.BLUE);
        board.setField(24, Mark.BLUE);
        board.setField(19, Mark.BLUE);

        assertEquals(18, board.completeSquare(13));
        assertEquals(18, board.completeSquare(24));
        assertEquals(18, board.completeSquare(19));
        assertEquals(18, board.completeSquare(18));
    }


    /**
     * Test of the CompleteHorizontal() method. The method should return the index of the left side inside the completed square.
     */
    @Test
    void testCompleteHorizontal() {
        board.setField(5, Mark.RED);
        board.setField(6, Mark.RED);
        board.setField(11, Mark.RED);
        board.setField(0, Mark.RED);

        assertEquals(5, board.completeHorizontalSquare(0));
        assertEquals(5, board.completeHorizontalSquare(11));

        board.setField(25, Mark.RED);
        board.setField(20, Mark.RED);
        board.setField(19, Mark.RED);
        board.setField(14, Mark.BLUE);

        assertEquals(19, board.completeHorizontalSquare(14));
        assertEquals(19, board.completeHorizontalSquare(25));

        board.setField(30, Mark.BLUE);
        board.setField(31, Mark.RED);
        board.setField(36, Mark.RED);

        assertEquals(30, board.completeHorizontalSquare(36));

        board.setField(33, Mark.RED);
        board.setField(38, Mark.RED);
        board.setField(39, Mark.RED);
        board.setField(49, Mark.RED);
        board.setField(50, Mark.RED);
        board.setField(55, Mark.RED);
        board.setField(44, Mark.BLUE);

        assertEquals(38, board.completeHorizontalSquare(44));
        assertEquals(38, board.completeHorizontalSquare(33));
        assertEquals(49, board.completeHorizontalSquare(55));


    }

    /**
     * Test of the CompleteVertical() method. The method should return the index of the left side inside the completed square.
     */
    @Test
    void testCompleteVertical() {
        board.setField(5, Mark.RED);
        board.setField(6, Mark.RED);
        board.setField(11, Mark.RED);
        board.setField(0, Mark.RED);

        assertEquals(5, board.completeVerticalSquare(6));
        assertEquals(5, board.completeVerticalSquare(5));
        assertEquals(5, board.completeSquare(5));
        assertTrue(board.getPointsContents().get(Mark.RED).contains(5));

        board.setField(56, Mark.RED);
        board.setField(50, Mark.RED);
        board.setField(45, Mark.RED);
        board.setField(46, Mark.RED);
        board.setField(52, Mark.RED);
        board.setField(57, Mark.RED);
        board.setField(51, Mark.RED);

        assertEquals(51, board.completeVerticalSquare(52));
        assertTrue(board.getPointsContents().get(Mark.RED).contains(51));
        assertEquals(51, board.completeVerticalSquare(51));
        assertTrue(board.getPointsContents().get(Mark.RED).contains(50));
    }

    /**
     * Test for the isWinner() method.
     * tests for the winner when board is all red, all blue, and mixed.
     */
    @Test
    void testIsWinner() {
        for (int i = 0; i < Board.INDEX; i++) {
            board.setField(i, Mark.RED);
        }
        assertTrue(board.isWinner(Mark.RED));
        assertFalse(board.isWinner(Mark.BLUE));
        assertFalse(board.isWinner(Mark.EMPTY));

        board.reset();

        for (int i = 0; i < Board.INDEX; i++) {
            board.setField(i, Mark.BLUE);
        }
        assertTrue(board.isWinner(Mark.BLUE));
        assertFalse(board.isWinner(Mark.RED));
        assertFalse(board.isWinner(Mark.EMPTY));

        board.reset();

        for (int i = 0; i < Board.INDEX; i++) {
            if (i <= Board.INDEX / 2) {
                board.setField(i, Mark.BLUE);
            } else {
                board.setField(i, Mark.RED);
            }
        }
        assertTrue(board.isWinner(Mark.RED));
    }

    /**
     * Test of the isField() method, which checks if the given index corresponds to a valid field on the board.
     */
    @Test
    void testIsField() {
        assertTrue(board.isField(0));
        assertTrue(board.isField(Board.INDEX - 1));
        assertTrue(board.isField(30));
        assertFalse(board.isField(-1));
        assertFalse(board.isField(Board.INDEX));
        assertFalse(board.isField(Board.INDEX * 2));
    }

    /**
     * Test of the isHorizontal() method, which checks if a certain index is horizontal.
     */
    @Test
    void testIsHorizontal() {
        assertTrue(board.isHorizontal(0));
        assertFalse(board.isHorizontal(5));
        assertTrue(board.isHorizontal(11));
        assertTrue(board.isHorizontal(Board.INDEX - 1));
        assertFalse(board.isHorizontal(Board.INDEX - Board.DIM));
    }

    /**
     * Test of the isVertical() method, which checks if a certain index is vertical.
     */
    @Test
    void testIsVertical() {
        assertFalse(board.isVertical(0));
        assertTrue(board.isVertical(5));
        assertFalse(board.isVertical(11));
        assertTrue(board.isVertical(Board.DIM));
        assertTrue(board.isVertical(Board.INDEX - Board.DIM));
    }

    /**
     * Test of the getPointsContents() method, which returns a copy of the points map.
     */
    @Test
    void testGetPointsContents() {
        Map<Mark, Set<Integer>> pointsContents = board.getPointsContents();

        assertNotNull(pointsContents);
        assertEquals(0, pointsContents.get(Mark.BLUE).size());
        assertEquals(0, pointsContents.get(Mark.RED).size());

        // Modify the original map, and check if the copy remains unchanged
        board.getPointsContents().get(Mark.BLUE).add(1);
        board.getPointsContents().get(Mark.RED).add(1);

        assertEquals(1, pointsContents.get(Mark.BLUE).size());
        assertEquals(1, pointsContents.get(Mark.RED).size());
    }

    /**
     * test to see if the toString method doesn't return null or an empty string
     */
    @Test
    void testToString(){
        assertNotNull(board.toString());
        assertNotEquals("",board.toString());
    }
}
