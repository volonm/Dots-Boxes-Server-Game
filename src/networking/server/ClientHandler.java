package networking.server;

import game.control.Player;
import game.model.Mark;
import game.model.Game;
import game.model.Move;
import networking.protocol.Protocol;

import java.util.Objects;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.ReentrantLock;

/**
 * The ClientHandler class is tasked for handling communication with a client.
 * It extends Thread and implements the Player interface to participate in a game.
 */
public class ClientHandler extends Thread implements Player {

    /**
     * Reference to the server instance.
     */
    private final GameServer server;

    /**
     * Reference to the ServerConnection instance.
     */
    private final ServerConnection serverConnection;

    /**
     * The field to store the username of the ClientHandler
     */
    private String username = null;

    /**
     * The field to store the description of the Client.
     */
    private String description = null;

    /**
     * The field to store the mark of the Client player.
     */
    private Mark mark = null;

    /**
     * The field to store the Move of the client player.
     */
    private Move moveBuffer = null;

    /**
     * Reentrant Lock to lock the moveBuffer.
     */
    private final ReentrantLock lock = new ReentrantLock();

    /**
     * Condition for the reentrant lock.
     */
    private final Condition moveUpdated = lock.newCondition();

    /**
     * Boolean field to indicate whether the client is in the game.
     */
    private boolean isInGame = false;

    /**
     * Boolean field to indicate whether the client has finalized the handshake.
     */
    private boolean helloProtocol = false;

    /**
     * Constructor to initialize the ClientHandler Object.
     *
     * @param gameServer    server instance.
     * @param serverConnect server connection class instance.
     */
    public ClientHandler(GameServer gameServer, ServerConnection serverConnect) {
        this.server = gameServer;
        this.serverConnection = serverConnect;
    }

    /**
     * Returns the username of the clientHandler, if there is no username registered yet, returns null.
     *
     * @return username of the clientHandler.
     */
    public String getUsername() {
        return username;
    }

    /**
     * Sets the given parameter username to the username of the clientHandler.
     *
     * @param username username to set.points.get(mark).add(completeSquare(index));
     */
    public void setUsername(String username) {
        this.username = username;
    }


    /**
     * Handles Hello message from the client, sets the received description of the client to ClientHandler,
     * and send the Hello by server and finalize the Handshake.
     *
     * @param description description of the client
     */
    public void handleHello(String description) {
        this.description = description;
        if (!this.helloProtocol) {
            System.out.println(Protocol.HELLO + Protocol.SEPARATOR + description);
            server.handleHelloToClient(this);
        } else sendCommand(Protocol.ERROR);
        this.helloProtocol = true;
    }


    /**
     * Handles the login command to the server
     *
     * @param username - received username to Login.
     */
    public void handleLogin(String username) {
        if (helloProtocol && !Objects.isNull(username)) {
            server.handleLogin(this, username);
        } else {
            sendCommand(Protocol.ERROR);
        }
    }

    /**
     * Handles the List command to the server, also checks whether the client is logged in.
     */
    public void handleList() {
        server.handleList(this);
    }

    /**
     * Handles the Queue command to the server from client, also check whether the client is logged in.
     * Double checks whether the client is in the Queue and logged in.
     */
    public void handleQueue() {
        if (server.isLoggedIn(this) && !server.checkUsername(getUsername())
                && !server.isInQueue(this) && !isInGame) {
            server.joinQueue(this);
        } else if(server.isLoggedIn(this) && !server.checkUsername(getUsername())
                && server.isInQueue(this) && !isInGame) {
            server.leaveQueue(this);
        }else {
            serverConnection.sendMessageClient(Protocol.ERROR);
        }
    }

    /**
     * Handles the Move command, updates the moveBuffer of the client to the game instance to do the move.
     * Implemented with reentrant lock with ensuring that it is released in the "finally" block.
     *
     * @param move move to play
     */
    public void handleMove(Move move) {
        if (isInGame) {
            lock.lock();
            try {
                moveBuffer = move;
                moveUpdated.signalAll(); // Signal the waiting thread in determineMove
            } finally {
                lock.unlock();
            }
        }
    }

    /**
     * Handles the New Game command sets the isInGame to true, because the client started new game.
     */
    public void handleNewGame() {
        this.isInGame = true;
    }

    /**
     * Handles the end of the Game for a client, namely sets the isInGame to false, because the client started new game.
     */
    public void handleEndGame() {
        this.isInGame = false;
    }


    /**
     * Sends hello to the client with the description of the server
     *
     * @param description description of the server.
     */
    public void sendHello(String description) {
        this.serverConnection.sendMessageClient(Protocol.HELLO + Protocol.SEPARATOR + description);
    }

    /**
     * Sends LOGIN to the client with the description of the server
     *
     * @param success description of the server.
     */
    public void sendLogin(boolean success) {
        if (success) this.serverConnection.sendMessageClient(Protocol.LOGIN);
        else this.serverConnection.sendMessageClient(Protocol.ALREADYLOGGEDIN);
    }

    /**
     * Sends the command to the client,double checks if the client is logged in to be sure that
     * it is not accessible before login, sends Error otherwise.
     *
     * @param command to send, ERROR if the client is not logged in.
     */
    public void sendCommand(String command) {
        if (server.isLoggedIn(this) && !server.checkUsername(getUsername())) {
            this.serverConnection.sendMessageClient(command);
        } else this.serverConnection.sendMessageClient(Protocol.ERROR);
    }


    /**
     * Sends the in game move to the client.
     *
     * @param move index of the move to send.
     */
    public void sendMove(int move) {
        if (server.isLoggedIn(this) && !server.checkUsername(getUsername()) && isInGame) {
            this.serverConnection.sendMessageClient(Protocol.MOVE + Protocol.SEPARATOR + move);
        } else this.serverConnection.sendMessageClient(Protocol.ERROR);
    }

    /**
     * Handles a disconnect from the server, i.e., when the server connection is closed.
     */
    protected void handleDisconnect() {
        // Remove the client from the server when disconnected
        server.removeClient(this);
        if (server.isInQueue(this)) {
            server.leaveQueue(this);
        }
        handleEndGame();
        lock.lock();
        try {
            moveUpdated.signalAll(); // Signal the waiting thread in determineMove
        } finally {
            lock.unlock();
        }
    }

    /**
     * Returns whether the client is in the game, true if the client has started game, false otherwise.
     *
     * @return true if the client is in the game.
     */
    public boolean isInGame() {
        return this.isInGame;
    }

    /**
     * The run method of the ClientHandler thread.
     * This method is not used explicitly, but it's present to support threading.
     */
    @Override
    public void run() {
        // Thread's run method, not used, but present so ClientHandler can be threaded
    }

    /**
     * Determines the move to be played by the client in the game.
     * It uses a reentrant lock to synchronize access to the moveBuffer and awaits a valid move or interruption.
     *
     * @param game The current state of the game.
     * @return The Move to be played by the client, or null if the client is not in the game.
     */
    @Override
    public Move determineMove(Game game) {
        lock.lock();
        try {
            while (!game.isValidMove(moveBuffer) && isInGame) {
                try {
                    moveUpdated.await();
                } catch (InterruptedException e) {
                    Thread.currentThread().interrupt();
                    sendCommand(Protocol.ERROR);
                }
                if (!game.isValidMove(moveBuffer)) sendCommand(Protocol.ERROR);
            }
            if (!isInGame) {
                return null;
            }
            Move validMove = moveBuffer;
            moveBuffer = null;
            return validMove;
        } finally {
            lock.unlock();
        }
    }

    /**
     * Returns whether the Hello message has taken place in the protocol,
     * returns true if the hello was sent previously, otherwise - false.
     *
     * @return true if the Hello has been received, false otherwise.
     */
    public boolean isHelloProtocol() {
        return this.helloProtocol;
    }

    /**
     * returns the mark of the ClientHandler
     *
     * @return the mark of the ClientHandler
     */
    @Override
    public Mark getMark() {
        return this.mark;
    }

    /**
     * Sets the mark of the clientHandler to the given mark for the game.
     *
     * @param m - mark to set
     */
    public void setMark(Mark m) {
        this.mark = m;
    }

    /**
     * returns the username of the client
     *
     * @return the username of the client
     */
    @Override
    public String toString() {
        return username;
    }


}
