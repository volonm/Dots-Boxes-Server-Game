package game.model;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * The Board class represents the game board for a game of dots & boxes.
 * It provides methods to interact with the board, set marks, check for wins,
 * and display the current state of the board.
 */
public class Board {

    /*@
      @ private invariant fields != null;
      @ private invariant points != null;
      @ private invariant points.containsKey(Mark.BLUE);
      @ private invariant points.containsKey(Mark.RED);
      @*/

    public static final int DIM = 6;
    public static final int INDEX = (DIM - 1) * DIM * 2;
    private final Mark[] fields;
    private final HashMap<Mark, Set<Integer>> points;

    /**
     * constructs a new board object
     */
    /*@
      @ ensures (\forall int i; 0 <= i && i < INDEX; getField(i) == Mark.EMPTY);
      @ ensures getPoints(Mark.BLUE) == 0;
      @ ensures getPoints(Mark.RED) == 0;
      @*/
    public Board() {
        fields = new Mark[INDEX];
        points = new HashMap<>();
        points.put(Mark.BLUE, new HashSet<>());
        points.put(Mark.RED, new HashSet<>());

        // Initialize the board to all EMPTY
        for (int i = 0; i < INDEX; i++) {
            fields[i] = Mark.EMPTY;
        }
    }

    /**
     * Creates a deep copy of the board.
     *
     * @return a new Board object with the same state as this board
     */
    /*@
      @ ensures \result != this;
      @ ensures (\forall int i; 0 <= i && i < INDEX; \result.getField(i) == getField(i));
      @ ensures \result.getPoints(Mark.BLUE) == getPoints(Mark.BLUE);
      @ ensures \result.getPoints(Mark.RED) == getPoints(Mark.RED);
      @ pure
    */
    public Board deepCopy() {
        Board copy = new Board();
        System.arraycopy(this.fields, 0, copy.fields, 0, INDEX);
        return copy;
    }


    /**
     * Checks if the given index corresponds to a valid field on the board.
     *
     * @param index the linear index
     * @return true if the index is a valid field, false otherwise
     */
    /*@
      @ requires index >= 0 && index < INDEX;
      @ ensures \result == (index >= 0 && index < INDEX);
      @ pure
      @*/
    public boolean isField(int index) {
        return index >= 0 && index < INDEX;
    }

    /**
     * Gets the mark at the specified index on the board.
     *
     * @param index the linear index
     * @return the mark at the specified index
     */
    /*@
      @ requires isField(index);
      @ ensures \result != null;
      @ pure
      @*/
    public Mark getField(int index) {
        return fields[index];
    }

    /**
     * Sets the mark at the specified index on the board.
     * And adds the left line of the square to the Hashmap for the points if a square is formed
     *
     * @param index the linear index
     * @param mark  the mark to set at the specified index
     */
    /*@
      @ requires isField(index) && isEmptyField(index);
      @ ensures getField(index) == mark;
      @ ensures completeSquare(index) > -1 ==> getPointsContents().containsValue(completeSquare(index));
      @*/
    public void setField(int index, Mark mark) {
        if (isField(index) && isEmptyField(index)) {
            fields[index] = mark;
            if (completeSquare(index) > -1) {
                points.get(mark).add(completeSquare(index));
            }
        }
    }

    /**
     * Checks if the given index corresponds to an empty field on the board.
     *
     * @param index the linear index
     * @return true if the field at the index is empty, false otherwise
     */
    /*@
      @ requires isField(index);
      @ ensures \result == (getField(index) == Mark.EMPTY);
      @ pure
      @*/
    public boolean isEmptyField(int index) {
        return isField(index) && getField(index) == Mark.EMPTY;
    }

    /**
     * Checks if the board is full (all fields are filled).
     *
     * @return true if the board is full, false otherwise
     */
    //@ ensures \result == (\forall int i; 0 <= i && i < INDEX; fields[i] != Mark.EMPTY);
    //@ pure
    public boolean isFull() {
        for (int i = 0; i < INDEX; i++) {
            if (fields[i] == Mark.EMPTY) {
                return false;
            }
        }
        return true;
    }

    /**
     * checks if a square is completed after a mark is placed on a certain index
     *
     * @param index the index of the placed mark
     * @return the index of the left line of the square or -1 if no square
     */
    /*@
      @ requires isField(index);
      @ ensures isHorizontal(index) && completeHorizontalSquare(index) > -1 ==> \result > -1;
      @ ensures isVertical(index) && completeVerticalSquare(index) > -1 ==> \result > -1;
      @ pure
      @*/
    public int completeSquare(int index) {
        // Check if the index is within the valid range
        if (!isField(index)) {
            return -1;
        }
        if (isHorizontal(index)) {
            return completeHorizontalSquare(index);
        } else if (isVertical(index)) {
            return completeVerticalSquare(index);
        }
        return -1;
    }

    /**
     * Checks if a square is completed after a mark is placed on a certain index that is horizontal.
     *
     * @param index the index of the placed mark
     * @return the index of the left line of the square or -1 if no square
     */
/*@
  @ requires isField(index);
  @ ensures (\result == -1) || ((lowerSquare(index) && upperSquare(index)) ==> (getPointsContents().containsValue(index + DIM - 1) && \result == index - DIM)) ||
            (lowerSquare(index) ==> (\result == index + DIM - 1)) ||
            (upperSquare(index) ==> (\result == index - DIM));
  @ pure
  @*/
    public int completeHorizontalSquare(int index) {
        if (lowerSquare(index) && upperSquare(index)) {
            points.get(getField(index)).add(index + DIM - 1);
            return index - DIM;
        } else if (lowerSquare(index)) {
            return index + DIM - 1;
        } else if (upperSquare(index)) {
            return index - DIM;
        }
        return -1;
    }

    /**
     * Checks if the lower square is completed after a mark is placed on a certain index that is horizontal.
     *
     * @param index the index of the placed mark
     * @return true if the lower square is completed, false otherwise
     */
/*@
  @ requires isField(index);
  @ ensures \result == (index < 49 &&
                       fields[index] != Mark.EMPTY && fields[index + 11] != Mark.EMPTY &&
                       fields[index + DIM - 1] != Mark.EMPTY && fields[index + DIM] != Mark.EMPTY);
  @*/
    private boolean lowerSquare(int index) {
        return index < 49 &&
                fields[index] != Mark.EMPTY && fields[index + 11] != Mark.EMPTY &&
                fields[index + DIM - 1] != Mark.EMPTY && fields[index + DIM] != Mark.EMPTY;
    }

    /**
     * Checks if the upper square is completed after a mark is placed on a certain index that is horizontal.
     *
     * @param index the index of the placed mark
     * @return true if the upper square is completed, false otherwise
     */
/*@
  @ requires isField(index);
  @ ensures \result == (index > DIM - 2 &&
                       fields[index] != Mark.EMPTY && fields[index - 11] != Mark.EMPTY &&
                       fields[index - DIM + 1] != Mark.EMPTY && fields[index - DIM] != Mark.EMPTY);
  @*/
    private boolean upperSquare(int index) {
        return index > DIM - 2 &&
                fields[index] != Mark.EMPTY && fields[index - 11] != Mark.EMPTY &&
                fields[index - DIM + 1] != Mark.EMPTY && fields[index - DIM] != Mark.EMPTY;
    }

    /**
     * Checks if a square is completed after a mark is placed on a certain index that is vertical.
     *
     * @param index the index of the placed mark
     * @return the index of the left line of the square or -1 if no square
     */
/*@
  @ requires isField(index);
  @ ensures (\result == -1) ||
           (rightSquare(index) && leftSquare(index) ==> (getPointsContents().containsValue(index - 1) && \result == index)) ||
           (rightSquare(index) ==> (\result == index)) ||
           (leftSquare(index) ==> (\result == index - 1));
  @ pure
  @*/
    public int completeVerticalSquare(int index) {
        if (rightSquare(index) && leftSquare(index)) {
            points.get(getField(index)).add(index - 1);
            return index;
        } else if (rightSquare(index)) {
            return index;
        } else if (leftSquare(index)) {
            return index - 1;
        }
        return -1;
    }

    /**
     * Checks if the right square is completed after a mark is placed on a certain index that is vertical.
     *
     * @param index the index of the placed mark
     * @return true if the right square is completed, false otherwise
     */
/*@
  @ requires isField(index);
  @ ensures \result == (index > 0 && index < INDEX - 1 &&
                       index % ((DIM * 2) - 1) != 10 &&
                       fields[index] != Mark.EMPTY && fields[index + 1] != Mark.EMPTY &&
                       fields[index - DIM + 1] != Mark.EMPTY && fields[index + DIM] != Mark.EMPTY);
  @*/
    private boolean rightSquare(int index) {
        return index > 0 && index < INDEX - 1 &&
                index % ((DIM * 2) - 1) != 10 &&
                fields[index] != Mark.EMPTY && fields[index + 1] != Mark.EMPTY &&
                fields[index - DIM + 1] != Mark.EMPTY && fields[index + DIM] != Mark.EMPTY;
    }

    /**
     * Checks if the left square is completed after a mark is placed on a certain index that is vertical.
     *
     * @param index the index of the placed mark
     * @return true if the left square is completed, false otherwise
     */
/*@
  @ requires isField(index);
  @ ensures \result == (index > 0 && index < INDEX - 1 &&
                       index % ((DIM * 2) - 1) != 5 &&
                       fields[index] != Mark.EMPTY && fields[index - 1] != Mark.EMPTY &&
                       fields[index - DIM] != Mark.EMPTY && fields[index + DIM - 1] != Mark.EMPTY);
  @*/
    private boolean leftSquare(int index) {
        return index > 0 && index < INDEX - 1 &&
                index % ((DIM * 2) - 1) != 5 &&
                fields[index] != Mark.EMPTY && fields[index - 1] != Mark.EMPTY &&
                fields[index - DIM] != Mark.EMPTY && fields[index + DIM - 1] != Mark.EMPTY;
    }

    /**
     * checks if a certain index is horizontal
     *
     * @param index the index to check
     * @return true if horizontal, false if vertical
     */
    /*@
      @ requires isField(index);
      @ ensures \result == (index % 11 < 5);
      @ pure
      @*/
    public boolean isHorizontal(int index) {
        int test = index % 11;
        return test < 5;
    }

    /**
     * checks if a certain index is vertical
     *
     * @param index the index to check
     * @return true if vertical, false if horizontal
     */
    /*@
      @ requires isField(index);
      @ ensures \result == (index % 11 > 4);
      @ pure
      @*/
    public boolean isVertical(int index) {
        int test = index % 11;
        return test > 4;
    }

    /**
     * Checks if the specified player (Mark) is a winner.
     *
     * @param player the player (Mark) to check for a win
     * @return true if the player is a winner, false otherwise
     */
    /*@
      @ requires player != null;
      @ ensures \result == (player != Mark.EMPTY && getPoints(player) > getPoints(player.other()));
      @ pure
      @*/
    public boolean isWinner(Mark player) {
        if (player != Mark.EMPTY) {
            return points.get(player).size() > points.get(player.other()).size();
        }
        return false;
    }

    /**
     * Resets the board to its initial state.
     */
    /*@
      @ ensures (\forall Mark m; m != null; getPoints(m) == 0);
      @ ensures (\forall int i; 0 <= i && i < INDEX; fields[i] == Mark.EMPTY);
      @*/
    public void reset() {
        for (int i = 0; i < INDEX; i++) {
            fields[i] = Mark.EMPTY;
        }
        points.get(Mark.RED).clear();
        points.get(Mark.BLUE).clear();
    }

    /**
     * String representation of the dots & boxes game
     *
     * @return the string representation of the board
     */
    /*@
      @ ensures \result != null;
      @*/
    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();

        for (int i = 0; i < INDEX; i++) {
            switch (i % 11) {
                case 0, 1, 2, 3, 4:
                    sb.append(colorize(i));
                    if (i == 4 || i == 15 || i == 26 || i == 37 || i == 48 || i == 59) {
                        sb.append("+\n");
                    }
                    break;
                case 5, 6, 7, 8, 9:
                    sb.append(colorizeVerticalLine(i));
                    break;
                case 10:
                    sb.append(colorizeVerticalLine(i));
                    sb.append("\n");
                    break;
                default:
            }
        }
        sb.append("Blue points: ").append(getPoints(Mark.BLUE)).append(" Red points: ").append(getPoints(Mark.RED));
        return sb.toString();
    }


    /**
     * gives color to horizontal marks
     *
     * @param index the index to color
     * @return the string representation of the colored mark
     */
    /*@
      @ requires 0 <= index && index < INDEX;
      @ ensures \result != null;
      @*/
    public String colorize(int index) {
        Mark mark = getField(index);
        switch (mark) {
            case EMPTY:
                if (index < 10) {
                    return "+--" + index + "--";
                } else {
                    return "+-" + index + "--";
                }
            case BLUE:
                return "+" + "\u001B[34m" + "-----" + "\u001B[0m";
            case RED:
                return "+" + "\u001B[31m" + "-----" + "\u001B[0m";
            default:
                return "     ";
        }
    }

    /**
     * gives color to vertical marks and also places an indicator in the square when complete
     *
     * @param index the index to color
     * @return the string representation of the colored mark and the square if complete
     */
    /*@
      @ requires 0 <= index && index < INDEX;
      @ ensures \result != null;
      @*/
    public String colorizeVerticalLine(int index) {
        Mark mark = getField(index);
        boolean isCompletedBlue = points.get(Mark.BLUE).contains(index);
        boolean isCompletedRed = points.get(Mark.RED).contains(index);

        switch (mark) {
            case EMPTY:
                if (index < 10) {
                    return "\u001B[0m" + "|" + index + "    " + "\u001B[0m";
                } else {
                    return "\u001B[0m" + "|" + index + "   " + "\u001B[0m";
                }
            case BLUE:
                if (isCompletedBlue) {
                    return "\u001B[34m" + "|  O  " + "\u001B[0m";
                } else if (isCompletedRed) {
                    return "\u001B[34m" + "|" + "\u001B[0m" + "\u001B[31m" + "  X  " + "\u001B[0m";
                }
                return "\u001B[34m" + "|     " + "\u001B[0m";
            case RED:
                if (isCompletedBlue) {
                    return "\u001B[31m" + "|" + "\u001B[0m" + "\u001B[34m" + "  O  " + "\u001B[0m";
                } else if (isCompletedRed) {
                    return "\u001B[31m" + "|  X  " + "\u001B[0m";
                }
                return "\u001B[31m" + "|     " + "\u001B[0m";
            default:
                return "     ";
        }
    }

    /**
     * Returns the number of points for the given mark.
     *
     * @param m - mark to calculate the points.
     * @return number of points.
     */
    /*@
      @ requires m != null;
      @ ensures \result >= 0;
      @ pure
      @*/
    public int getPoints(Mark m) {
        if (points.get(m).isEmpty() || points.get(m) == null) return 0;
        else return points.get(m).size();
    }

    /**
     * Returns a copy of the points map, containing the contents of points for each Mark.
     * The returned map is a shallow copy, and modifications to it will not affect the original points map.
     *
     * @return a copy of the points map, containing the contents of points for each Mark
     */
    /*@
      @ ensures \result != null;
      @ ensures (\forall Mark m; m != null; \result.containsKey(m) && ( getPoints(m) == 0));
      @ pure
      @*/
    public Map<Mark, Set<Integer>> getPointsContents() {
        return points;
    }
}
