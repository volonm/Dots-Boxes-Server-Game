package networking.server;

import game.model.GameImpl;
import game.model.Mark;
import game.model.Move;
import networking.protocol.Protocol;

/**
 * A class representing the server-side logic for a Dots and Boxes game.
 * Manages the game state and communication with the players.
 */
public class GameImplServer implements Runnable {

    /**
     * Field to store the game.
     */
    private final GameImpl game;

    /**
     * Field to store the clients of the game
     */
    private final ClientHandler[] clients;

    /**
     * Constructs a GameImplServer instance with two clients representing players.
     *
     * @param player1Client The ClientHandler for the first player.
     * @param player2Client The ClientHandler for the second player.
     */
    public GameImplServer(ClientHandler player1Client, ClientHandler player2Client) {
        player1Client.setMark(Mark.RED);
        player2Client.setMark(Mark.BLUE);
        game = new GameImpl(player1Client, player2Client);
        clients = new ClientHandler[]{player1Client, player2Client};
    }

    /**
     * The main logic for running the game in a separate thread.
     * Continues until the game is over or one of the players disconnects.
     * Handles player turns and sends moves to clients.
     */
    @Override
    public void run() {
        while (!game.isGameOver() && clients[0].isInGame() && clients[1].isInGame()) {
            Move move = game.getTurn().determineMove(game);
            if (move != null && game.isValidMove(move)) {
                game.doMove(move);
                if (!game.completesSquare(move.getIndex())) {
                    game.changeTurn();
                }
                sendMove(move.getIndex());
            }
        }
        sendGameOver();
    }

    /**
     * Redirects the move to all the players in game.
     *
     * @param move move that was played.
     */
    public void sendMove(int move) {
        for (ClientHandler client : clients) {
            client.sendMove(move);
        }
    }

    /**
     * Sends the result of the Game to both players, checks whether the reason is
     * disconnected or normal e.g. Victory or Draw.
     */
    public void sendGameOver() {
        String result = Protocol.GAMEOVER + Protocol.SEPARATOR;
        if (clients[0].isInGame() && clients[1].isInGame()) {
            if (game.getWinner().toString().equals(clients[0].getUsername())) {
                result += Protocol.VICTORY + Protocol.SEPARATOR + clients[0].getUsername();
            } else if (game.getWinner().toString().equals(clients[1].getUsername())) {
                result += Protocol.VICTORY + Protocol.SEPARATOR + clients[1].getUsername();
            }
        } else {
            if (!clients[0].isInGame()) {
                result += Protocol.DISCONNECT + Protocol.SEPARATOR + clients[1].getUsername();
            } else {
                result += Protocol.DISCONNECT + Protocol.SEPARATOR + clients[0].getUsername();
            }
        }
        for (ClientHandler client : clients) {
            client.handleEndGame();
            client.sendCommand(result);
        }
    }
}
