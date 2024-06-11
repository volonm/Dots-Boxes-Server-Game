import game.control.HumanPlayer;
import game.control.Player;
import game.model.GameImpl;
import game.model.Mark;
import game.model.Move;
import networking.protocol.Protocol;
import networking.server.GameServer;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.*;
import java.net.InetAddress;
import java.net.Socket;
import java.util.List;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.*;

/**
 * test for the server protocol and to play a full game on the server
 * sometimes needs to be run multiple times since it can get stuck on testDoMove
 */
 class GameServerTest {

    /**
     * Field to store the server instance.
     */
    private GameServer server;

    /**
     * Constant field that represents the description of the server.
     */
    private static final String serverDescription = "My Server Test";

    /**
     * Initializes the server before each test with the given constant description with
     * or without extensions and random port.
     *
     * @throws IOException If an I/O error occurs when opening the server socket.
     */
    @BeforeEach
    void setUp() throws IOException {
        server = new GameServer(0, serverDescription);
    }

    /**
     * starts accepting connections for the other tests to function
     */
    private void acceptConnections() {
        try {
            server.acceptConnections();
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    /**
     * Tests the handling of the HELLO protocol command and several other conditions.
     *
     * @throws IOException If an I/O error occurs when opening the server socket.
     */
    @Test
    void testHello() throws IOException {
        assertTrue(server.getPort() > 0);
        assertTrue(server.getPort() <= 65535);

        // start the server
        new Thread(this::acceptConnections).start();
        Socket socket = new Socket(InetAddress.getLocalHost(), server.getPort());  // connect to the server
        String s;

        try (BufferedReader bufferedReader = new BufferedReader(new InputStreamReader(socket.getInputStream()));
             PrintWriter printWriter = new PrintWriter(new OutputStreamWriter(socket.getOutputStream()), true)) {
            // Handling the Hello client with no extensions.
            printWriter.println("HELLO~MyClientDescription");
            s = bufferedReader.readLine();
            assertEquals(Protocol.HELLO + Protocol.SEPARATOR + serverDescription, s);

            // Testing the second or third hello from the client. Which has to be
            // Error since hello has already taken place.
            printWriter.println("HELLO~MyClientDescription");
            s = bufferedReader.readLine();
            assertEquals(Protocol.ERROR, s);

            // Close the connection.
            socket.close();
        } finally {
            // Stop the server.
            server.close();
        }
    }

    /**
     * Test of handling the LOGIN Protocol command and how the ALREADYLOGGEDIN is sent by the
     * server when trying consecutive LOGIN command.
     *
     * @throws IOException If an I/O error occurs when opening the server socket.
     */
    @Test
    void testLogin() throws IOException {
        assertTrue(server.getPort() > 0);
        assertTrue(server.getPort() <= 65535);
        String username1 = "User1";

        // start the server
        new Thread(this::acceptConnections).start();
        Socket socket = new Socket(InetAddress.getLocalHost(), server.getPort());  // connect to the server
        String s;

        try (BufferedReader bufferedReader = new BufferedReader(new InputStreamReader(socket.getInputStream()));
             PrintWriter printWriter = new PrintWriter(new OutputStreamWriter(socket.getOutputStream()), true)) {

            // Handling the LOGIN before HELLO command has to reply with ERROR.
            printWriter.println(Protocol.LOGIN + Protocol.SEPARATOR + username1);
            s = bufferedReader.readLine();
            assertEquals(Protocol.ERROR, s);

            // Handling the Hello client with no extensions.
            printWriter.println(Protocol.HELLO + Protocol.SEPARATOR + "MyClientDescription");
            s = bufferedReader.readLine();
            assertEquals(Protocol.HELLO + Protocol.SEPARATOR + serverDescription, s);

            //Testing the Pure Login without the nickname
            printWriter.println(Protocol.LOGIN + Protocol.SEPARATOR);
            s = bufferedReader.readLine();
            assertEquals(Protocol.ERROR, s);

            // Testing the initial Login
            printWriter.println(Protocol.LOGIN + Protocol.SEPARATOR + username1);
            s = bufferedReader.readLine();
            assertEquals(Protocol.LOGIN, s);

            // Testing ALREADYLOGGEDIN exception send from the server.
            printWriter.println(Protocol.LOGIN + Protocol.SEPARATOR + username1);
            s = bufferedReader.readLine();
            assertEquals(Protocol.ALREADYLOGGEDIN, s);

            // Close the connection.
            socket.close();
        } finally {
            // Stop the server.
            server.close();
        }

    }


    /**
     * Test of handling the LOGIN Protocol command with multiple clients and how
     * the ALREADYLOGGEDIN is sent to the second client when there exists a user with this username.
     *
     * @throws IOException If an I/O error occurs when opening the server socket.
     */
    @Test
    void testLoginMultipleNames() throws IOException {
        assertTrue(server.getPort() > 0);
        assertTrue(server.getPort() <= 65535);
        String username1 = "User1";
        String username2 = "User2";
        String s1;
        String s2;
        // start the server
        new Thread(this::acceptConnections).start();

        Socket socket1 = new Socket(InetAddress.getLocalHost(), server.getPort());
        Socket socket2 = new Socket(InetAddress.getLocalHost(), server.getPort());

        try (BufferedReader bfr1 = new BufferedReader(new InputStreamReader(socket1.getInputStream()));
             PrintWriter pw1 = new PrintWriter(new OutputStreamWriter(socket1.getOutputStream()), true);
             BufferedReader bfr2 = new BufferedReader(new InputStreamReader(socket2.getInputStream()));
             PrintWriter pw2 = new PrintWriter(new OutputStreamWriter(socket2.getOutputStream()), true)) {


            // Handling the Hello for client1 with no extensions.
            pw1.println(Protocol.HELLO + Protocol.SEPARATOR + "MyClientDescription1");
            s1 = bfr1.readLine();
            assertEquals(Protocol.HELLO + Protocol.SEPARATOR + serverDescription, s1);

            // Handling the Hello for client1 with no extensions.
            pw2.println(Protocol.HELLO + Protocol.SEPARATOR + "MyClientDescription2");
            s2 = bfr2.readLine();
            assertEquals(Protocol.HELLO + Protocol.SEPARATOR + serverDescription, s2);

            //Testing the Pure Login without the nickname for both clients.
            pw1.println(Protocol.LOGIN + Protocol.SEPARATOR);
            s1 = bfr1.readLine();
            assertEquals(Protocol.ERROR, s1);
            pw2.println(Protocol.LOGIN + Protocol.SEPARATOR);
            s2 = bfr2.readLine();
            assertEquals(Protocol.ERROR, s2);

            // Testing the initial Login for client1
            pw1.println(Protocol.LOGIN + Protocol.SEPARATOR + username1);
            s1 = bfr1.readLine();
            assertEquals(Protocol.LOGIN, s1);

            // Testing ALREADYLOGGEDIN exception send from the server, because of the same username.
            pw2.println(Protocol.LOGIN + Protocol.SEPARATOR + username1);
            s2 = bfr2.readLine();
            assertEquals(Protocol.ALREADYLOGGEDIN, s2);

            // Testing whether the user2 can still login but with different username.
            pw2.println(Protocol.LOGIN + Protocol.SEPARATOR + username2);
            s2 = bfr2.readLine();
            assertEquals(Protocol.LOGIN, s2);

            // Close the connections.
            socket1.close();
            socket2.close();
        } finally {
            // Stop the server.
            server.close();
        }

    }


    /**
     * Test of the List Command with 3-4 clients.
     *
     * @throws IOException If an I/O error occurs when opening the server socket.
     */
    @Test
    void testList() throws IOException {
        assertTrue(server.getPort() > 0);
        assertTrue(server.getPort() <= 65535);
        String username1 = "User1";
        String username2 = "User2";
        String username3 = "User3";
        String username4 = "User4";
        String s1;
        String s2;
        String s3;
        String s4;
        // start the server
        new Thread(this::acceptConnections).start();

        // Sockets imitating the client connections
        Socket socket1 = new Socket(InetAddress.getLocalHost(), server.getPort());
        Socket socket2 = new Socket(InetAddress.getLocalHost(), server.getPort());
        Socket socket3 = new Socket(InetAddress.getLocalHost(), server.getPort());
        Socket socket4 = new Socket(InetAddress.getLocalHost(), server.getPort());

        // Try to create a BufferedReader and PrintWriter to track the Input/Output streams of each socket
        try (// I/O for client imitation 1, namely socket1
             BufferedReader bfr1 = new BufferedReader(new InputStreamReader(socket1.getInputStream()));
             PrintWriter pw1 = new PrintWriter(new OutputStreamWriter(socket1.getOutputStream()), true);

             // I/O for client imitation 2, namely socket2
             BufferedReader bfr2 = new BufferedReader(new InputStreamReader(socket2.getInputStream()));
             PrintWriter pw2 = new PrintWriter(new OutputStreamWriter(socket2.getOutputStream()), true);

             // I/O for client imitation 3, namely socket3
             BufferedReader bfr3 = new BufferedReader(new InputStreamReader(socket3.getInputStream()));
             PrintWriter pw3 = new PrintWriter(new OutputStreamWriter(socket3.getOutputStream()), true);

             // I/O for client imitation 4, namely socket4
             BufferedReader bfr4 = new BufferedReader(new InputStreamReader(socket4.getInputStream()));
             PrintWriter pw4 = new PrintWriter(new OutputStreamWriter(socket4.getOutputStream()), true)) {

            //Check that the list throws error when the client's not logged in

            pw4.println(Protocol.LIST);
            s4 = bfr4.readLine();
            assertEquals(Protocol.ERROR, s4);
            pw2.println(Protocol.LIST);
            s2 = bfr2.readLine();
            assertEquals(Protocol.ERROR, s2);

            // Handling the Hello for 3 clients with no extensions.

            //Client 1
            pw1.println(Protocol.HELLO + Protocol.SEPARATOR + "MyClientDescription1");
            s1 = bfr1.readLine();
            assertEquals(Protocol.HELLO + Protocol.SEPARATOR + serverDescription, s1);

            //Client 2
            pw2.println(Protocol.HELLO + Protocol.SEPARATOR + "MyClientDescription2");
            s2 = bfr2.readLine();
            assertEquals(Protocol.HELLO + Protocol.SEPARATOR + serverDescription, s2);

            //Client 3
            pw3.println(Protocol.HELLO + Protocol.SEPARATOR + "MyClientDescription3");
            s3 = bfr3.readLine();
            assertEquals(Protocol.HELLO + Protocol.SEPARATOR + serverDescription, s3);

            //Client 4
            pw4.println(Protocol.HELLO + Protocol.SEPARATOR + "MyClientDescription4");
            s4 = bfr4.readLine();
            assertEquals(Protocol.HELLO + Protocol.SEPARATOR + serverDescription, s4);


            // LOGIN Client 1 and check of the list command
            pw1.println(Protocol.LOGIN + Protocol.SEPARATOR + username1);
            s1 = bfr1.readLine();
            assertEquals(Protocol.LOGIN, s1);
            pw1.println(Protocol.LIST);
            s1 = bfr1.readLine();
            assertEquals(Protocol.LIST + Protocol.SEPARATOR + username1, s1);

            // LOGIN Client 2 and check if the list contains all users and result of List is the same for each client
            pw2.println(Protocol.LOGIN + Protocol.SEPARATOR + username2);
            s2 = bfr2.readLine();
            assertEquals(Protocol.LOGIN, s2);

            // List for client number 2
            pw2.println(Protocol.LIST);
            s2 = bfr2.readLine();
            assertTrue(s2.contains(username1));
            assertTrue(s2.contains(username2));

            // List for client number 1
            pw1.println(Protocol.LIST);
            s1 = bfr1.readLine();
            assertTrue(s1.contains(username1));
            assertTrue(s1.contains(username2));


            // LOGIN Client 3 and check of the list command
            pw3.println(Protocol.LOGIN + Protocol.SEPARATOR + username3);
            s3 = bfr3.readLine();
            assertEquals(Protocol.LOGIN, s3);

            // List for client number 3
            pw3.println(Protocol.LIST);
            s3 = bfr3.readLine();
            assertTrue(s3.contains(username1));
            assertTrue(s3.contains(username2));
            assertTrue(s3.contains(username3));

            // List for client number 2
            pw2.println(Protocol.LIST);
            s2 = bfr2.readLine();
            assertTrue(s2.contains(username1));
            assertTrue(s2.contains(username2));
            assertTrue(s2.contains(username3));

            // List for client number 1
            pw1.println(Protocol.LIST);
            s1 = bfr1.readLine();
            assertTrue(s1.contains(username1));
            assertTrue(s1.contains(username2));
            assertTrue(s1.contains(username3));


            // LOGIN Client 4 and check of the list command
            pw4.println(Protocol.LOGIN + Protocol.SEPARATOR + username4);
            s4 = bfr4.readLine();
            assertEquals(Protocol.LOGIN, s4);

            // List for client number 3
            pw3.println(Protocol.LIST);
            s3 = bfr3.readLine();
            assertTrue(s3.contains(username1));
            assertTrue(s3.contains(username2));
            assertTrue(s3.contains(username3));
            assertTrue(s3.contains(username4));

            // List for client number 2
            pw2.println(Protocol.LIST);
            s2 = bfr2.readLine();
            assertTrue(s2.contains(username1));
            assertTrue(s2.contains(username2));
            assertTrue(s2.contains(username3));
            assertTrue(s2.contains(username4));

            // List for client number 1
            pw1.println(Protocol.LIST);
            s1 = bfr1.readLine();
            assertTrue(s1.contains(username1));
            assertTrue(s1.contains(username2));
            assertTrue(s1.contains(username3));
            assertTrue(s1.contains(username4));

            // List for client number 4 after login
            pw4.println(Protocol.LIST);
            s4 = bfr4.readLine();
            assertTrue(s4.contains(username1));
            assertTrue(s4.contains(username2));
            assertTrue(s4.contains(username3));
            assertTrue(s4.contains(username4));


            // Close the connections.
            socket1.close();
            socket2.close();
            socket3.close();
            socket4.close();
        } finally {
            // Stop the server.
            server.close();
        }
    }

    /**
     * Login 2 clients and tries to join the queue and start a new game. Also checks whether the
     * LIST is accessible after new game and that QUEUE is not accessible while in game.
     */
    @Test
    void queueNewGameTest() throws IOException {
        assertTrue(server.getPort() > 0);
        assertTrue(server.getPort() <= 65535);
        String username1 = "User1";
        String username2 = "User2";
        String s1;
        String s2;
        // start the server
        new Thread(this::acceptConnections).start();

        // Sockets imitating the client connections
        Socket socket1 = new Socket(InetAddress.getLocalHost(), server.getPort());
        Socket socket2 = new Socket(InetAddress.getLocalHost(), server.getPort());
        try (// I/O for client imitation 1, namely socket1
             BufferedReader bfr1 = new BufferedReader(new InputStreamReader(socket1.getInputStream()));
             PrintWriter pw1 = new PrintWriter(new OutputStreamWriter(socket1.getOutputStream()), true);

             // I/O for client imitation 2, namely socket2
             BufferedReader bfr2 = new BufferedReader(new InputStreamReader(socket2.getInputStream()));
             PrintWriter pw2 = new PrintWriter(new OutputStreamWriter(socket2.getOutputStream()), true)) {

            //Client 1 Hello
            pw1.println(Protocol.HELLO + Protocol.SEPARATOR + "MyClientDescription1");
            s1 = bfr1.readLine();
            assertEquals(Protocol.HELLO + Protocol.SEPARATOR + serverDescription, s1);

            //Client 2 Hello
            pw2.println(Protocol.HELLO + Protocol.SEPARATOR + "MyClientDescription2");
            s2 = bfr2.readLine();
            assertEquals(Protocol.HELLO + Protocol.SEPARATOR + serverDescription, s2);


            // LOGIN Client 1 and join the queue
            pw1.println(Protocol.LOGIN + Protocol.SEPARATOR + username1);
            s1 = bfr1.readLine();
            assertEquals(Protocol.LOGIN, s1);
            pw1.println(Protocol.QUEUE);

            // LOGIN Client 2 and check if the list contains all users and result of List is the same for each client
            pw2.println(Protocol.LOGIN + Protocol.SEPARATOR + username2);
            s2 = bfr2.readLine();
            assertEquals(Protocol.LOGIN, s2);
            pw2.println(Protocol.QUEUE);

            s1 = bfr1.readLine();
            s2 = bfr2.readLine();

            // General check on received NEW GAME and that the names are correct.
            assertTrue(s1.contains(Protocol.NEWGAME));
            assertTrue(s2.contains(Protocol.NEWGAME));
            assertTrue(s1.contains(username1));
            assertTrue(s1.contains(username2));
            assertTrue(s2.contains(username1));
            assertTrue(s2.contains(username2));

            String[] partsFromClient1 = s1.split(Protocol.SEPARATOR);
            String[] partsFromClient2 = s2.split(Protocol.SEPARATOR);

            //Checking the correct format of the server reply
            assertArrayEquals(partsFromClient1, partsFromClient2);
            assertEquals(Protocol.NEWGAME, partsFromClient1[0]);
            assertEquals(Protocol.NEWGAME, partsFromClient2[0]);
            assertEquals(username1, partsFromClient1[1]);
            assertEquals(username1, partsFromClient2[1]);
            assertEquals(username2, partsFromClient1[2]);
            assertEquals(username2, partsFromClient2[2]);

            //Check whether the clients can access the LIST command.
            pw1.println(Protocol.LIST);
            s1 = bfr1.readLine();
            pw2.println(Protocol.LIST);
            s2 = bfr2.readLine();
            assertTrue(s1.contains(username1) && s1.contains(username2) && s1.contains(Protocol.LIST));
            assertTrue(s2.contains(username1) && s2.contains(username2) && s2.contains(Protocol.LIST));

            //Check whether the server is ready to throw an error when users try to join queue by command QUEUE.
            pw1.println(Protocol.QUEUE);
            s1 = bfr1.readLine();
            pw2.println(Protocol.QUEUE);
            s2 = bfr2.readLine();

            assertEquals(Protocol.ERROR, s1);
            assertEquals(Protocol.ERROR, s2);

            // Close the connections.
            socket1.close();
            socket2.close();
        } finally {
            // Stop the server.
            server.close();
        }
    }

    /**
     * Test that logins 2 clients, joins the game and tries to play game
     * according to the game's logic and tries
     * with different moves including invalid.
     */
    @Test
    void testDoMove() throws IOException {
        assertTrue(server.getPort() > 0);
        assertTrue(server.getPort() <= 65535);
        String username1 = "User1";
        String username2 = "User2";
        String s1;
        String s2;
        // start the server
        new Thread(this::acceptConnections).start();

        // Sockets imitating the client connections
        Socket socket1 = new Socket(InetAddress.getLocalHost(), server.getPort());
        Socket socket2 = new Socket(InetAddress.getLocalHost(), server.getPort());
        try (// I/O for client imitation 1, namely socket1
             BufferedReader bfr1 = new BufferedReader(new InputStreamReader(socket1.getInputStream()));
             PrintWriter pw1 = new PrintWriter(new OutputStreamWriter(socket1.getOutputStream()), true);

             // I/O for client imitation 2, namely socket2
             BufferedReader bfr2 = new BufferedReader(new InputStreamReader(socket2.getInputStream()));
             PrintWriter pw2 = new PrintWriter(new OutputStreamWriter(socket2.getOutputStream()), true)) {

            //Client 1 Hello
            pw1.println(Protocol.HELLO + Protocol.SEPARATOR + "MyClientDescription1");
            s1 = bfr1.readLine();
            assertEquals(Protocol.HELLO + Protocol.SEPARATOR + serverDescription, s1);

            //Client 2 Hello
            pw2.println(Protocol.HELLO + Protocol.SEPARATOR + "MyClientDescription2");
            s2 = bfr2.readLine();
            assertEquals(Protocol.HELLO + Protocol.SEPARATOR + serverDescription, s2);


            // LOGIN Client 1 and join the queue
            pw1.println(Protocol.LOGIN + Protocol.SEPARATOR + username1);
            s1 = bfr1.readLine();
            assertEquals(Protocol.LOGIN, s1);
            pw1.println(Protocol.QUEUE);

            // LOGIN Client 2 and check if the list contains all users and result of List is the same for each client
            pw2.println(Protocol.LOGIN + Protocol.SEPARATOR + username2);
            s2 = bfr2.readLine();
            assertEquals(Protocol.LOGIN, s2);
            pw2.println(Protocol.QUEUE);

            //Clean the BufferReaders from NEW GAME message.
            bfr2.readLine();
            bfr1.readLine();

            // Do the invalid move according to the game logic and inserting just random String.
            pw1.println(Protocol.MOVE + Protocol.SEPARATOR + "-1");
            s1 = bfr1.readLine();
            assertEquals(Protocol.ERROR, s1);
            pw1.println(Protocol.MOVE + Protocol.SEPARATOR + "321313123123");
            s1 = bfr1.readLine();
            assertEquals(Protocol.ERROR, s1);
            pw1.println(Protocol.MOVE + Protocol.SEPARATOR + "RANDOM STRING");
            s1 = bfr1.readLine();
            assertEquals(Protocol.ERROR, s1);
            pw1.println(Protocol.MOVE + Protocol.SEPARATOR + "-15412512521");
            s1 = bfr1.readLine();
            assertEquals(Protocol.ERROR, s1);

            // Play a valid move in the game and check whether all the clients get it (client 1)
            pw1.println(Protocol.MOVE + Protocol.SEPARATOR + "32");
            s1 = bfr1.readLine();
            s2 = bfr2.readLine();

            assertEquals(Protocol.MOVE + Protocol.SEPARATOR + "32", s1);
            assertEquals(Protocol.MOVE + Protocol.SEPARATOR + "32", s2);

            // Play next move from another player (client2)
            pw2.println(Protocol.MOVE + Protocol.SEPARATOR + "37");
            s1 = bfr1.readLine();
            s2 = bfr2.readLine();

            assertEquals(Protocol.MOVE + Protocol.SEPARATOR + "37", s1);
            assertEquals(Protocol.MOVE + Protocol.SEPARATOR + "37", s2);


            // Test if the same move as opponent's throws and error. (client 1)
            pw1.println(Protocol.MOVE + Protocol.SEPARATOR + "37");
            s1 = bfr1.readLine();
            assertEquals(Protocol.ERROR, s1);

            // Test if the completed square gives an extra move (client 1)
            pw1.println(Protocol.MOVE + Protocol.SEPARATOR + "26");
            s1 = bfr1.readLine();
            s2 = bfr2.readLine();
            assertEquals(Protocol.MOVE + Protocol.SEPARATOR + "26", s1);
            assertEquals(Protocol.MOVE + Protocol.SEPARATOR + "26", s2);
            // Client 2 here finishes the square.
            pw2.println(Protocol.MOVE + Protocol.SEPARATOR + "31");
            s1 = bfr1.readLine();
            s2 = bfr2.readLine();
            assertEquals(Protocol.MOVE + Protocol.SEPARATOR + "31", s1);
            assertEquals(Protocol.MOVE + Protocol.SEPARATOR + "31", s2);
            //same client sends next move because he completed square
            pw2.println(Protocol.MOVE + Protocol.SEPARATOR + "0");
            s1 = bfr1.readLine();
            s2 = bfr2.readLine();
            assertEquals(Protocol.MOVE + Protocol.SEPARATOR + "0", s1);
            assertEquals(Protocol.MOVE + Protocol.SEPARATOR + "0", s2);

        } finally {
            // Stop the server.
            server.close();
        }
    }


    @Test
    void testPlayFullGame() throws IOException {
        assertTrue(server.getPort() > 0);
        assertTrue(server.getPort() <= 65535);
        String username1 = "User1";
        String username2 = "User2";
        String s1;
        String s2;
        // start the server
        new Thread(this::acceptConnections).start();

        // Sockets imitating the client connections
        Socket socket1 = new Socket(InetAddress.getLocalHost(), server.getPort());
        Socket socket2 = new Socket(InetAddress.getLocalHost(), server.getPort());
        try (// I/O for client imitation 1, namely socket1
             BufferedReader bfr1 = new BufferedReader(new InputStreamReader(socket1.getInputStream()));
             PrintWriter pw1 = new PrintWriter(new OutputStreamWriter(socket1.getOutputStream()), true);

             // I/O for client imitation 2, namely socket2
             BufferedReader bfr2 = new BufferedReader(new InputStreamReader(socket2.getInputStream()));
             PrintWriter pw2 = new PrintWriter(new OutputStreamWriter(socket2.getOutputStream()), true)) {

            //Client 1 Hello
            pw1.println(Protocol.HELLO + Protocol.SEPARATOR + "MyClientDescription1");
            s1 = bfr1.readLine();
            assertEquals(Protocol.HELLO + Protocol.SEPARATOR + serverDescription, s1);

            //Client 2 Hello
            pw2.println(Protocol.HELLO + Protocol.SEPARATOR + "MyClientDescription2");
            s2 = bfr2.readLine();
            assertEquals(Protocol.HELLO + Protocol.SEPARATOR + serverDescription, s2);


            // LOGIN Client 1 and join the queue
            pw1.println(Protocol.LOGIN + Protocol.SEPARATOR + username1);
            s1 = bfr1.readLine();
            assertEquals(Protocol.LOGIN, s1);
            pw1.println(Protocol.QUEUE);

            // LOGIN Client 2 and join the Queue
            pw2.println(Protocol.LOGIN + Protocol.SEPARATOR + username2);
            s2 = bfr2.readLine();
            assertEquals(Protocol.LOGIN, s2);
            pw2.println(Protocol.QUEUE);

            //Creating two game instances just to fill the property in constructor.
            Player pl1 = new HumanPlayer(username1, Mark.BLUE);
            Player pl2 = new HumanPlayer(username2, Mark.RED);

            //Creating the game instance to keep track of it in the test.
            GameImpl game = new GameImpl(pl1, pl2);
            bfr1.readLine();
            bfr2.readLine();
            while (!game.isGameOver()) {
                Move move;
                List<Move> validMoves = game.getValidMoves();
                move = validMoves.get(new Random().nextInt(validMoves.size()));
                game.doMove(move);
                if (game.getTurn().equals(pl1)) {
                    String moveToSend = Protocol.MOVE + Protocol.SEPARATOR + move.getIndex();
                    pw1.println(moveToSend);

                    //check the buffers
                    s1 = bfr1.readLine();
                    s2 = bfr2.readLine();
                    assertEquals(moveToSend, s1);
                    assertEquals(moveToSend, s2);
                } else {
                    String moveToSend = Protocol.MOVE + Protocol.SEPARATOR + move.getIndex();
                    pw2.println(moveToSend);

                    //check the buffers
                    s2 = bfr2.readLine();
                    s1 = bfr1.readLine();
                    assertEquals(moveToSend, s1);
                    assertEquals(moveToSend, s2);
                }
                if (!game.completesSquare(move.getIndex())) game.changeTurn();

            }

            //Check that there is a winner, since in our 6x6 dots dimension there always will exist a winner.
            s2 = bfr2.readLine();
            s1 = bfr1.readLine();

            s2 = s2.replace(Protocol.GAMEOVER + Protocol.SEPARATOR + Protocol.VICTORY + Protocol.SEPARATOR, "");
            s1 = s1.replace(Protocol.GAMEOVER + Protocol.SEPARATOR + Protocol.VICTORY + Protocol.SEPARATOR, "");

            assertNotNull(game.getWinner());
            assertEquals(s2, game.getWinner().getName());
            assertEquals(s1, game.getWinner().getName());
            assertTrue((s2.equals(pl1.getName()) && s1.equals(pl1.getName()) || (s1.equals(pl2.getName()) || s2.equals(pl2.getName()))));
            assertEquals(s1,s2);


            // Check if the game has really ended.
            assertTrue(game.getValidMoves().isEmpty());
            assertTrue(game.isGameOver());

            /* Check whether the queue and playing remains same even after the game ended.
            Play the game again after the game was played, however this time the first player is the second client.
             */
            game = new GameImpl(pl2, pl1);
            //Join Queue again
            pw2.println(Protocol.QUEUE);
            pw1.println(Protocol.QUEUE);

            //Check that NewGame is created.
            s1 = bfr1.readLine();
            s2 = bfr2.readLine();

            assertTrue(s1.contains(Protocol.NEWGAME));
            assertTrue(s2.contains(Protocol.NEWGAME));
            assertTrue(s1.contains(username1));
            assertTrue(s1.contains(username2));
            assertTrue(s2.contains(username1));
            assertTrue(s2.contains(username2));


            while (!game.isGameOver()) {
                Move move;
                List<Move> validMoves = game.getValidMoves();
                move = validMoves.get(new Random().nextInt(validMoves.size()));
                game.doMove(move);
                if (game.getTurn().equals(pl1)) {
                    String moveToSend = Protocol.MOVE + Protocol.SEPARATOR + move.getIndex();
                    pw1.println(moveToSend);

                    //check the buffers
                    s1 = bfr1.readLine();
                    s2 = bfr2.readLine();
                    assertEquals(moveToSend, s1);
                    assertEquals(moveToSend, s2);
                } else {
                    String moveToSend = Protocol.MOVE + Protocol.SEPARATOR + move.getIndex();
                    pw2.println(moveToSend);
                    //check the buffers
                    s2 = bfr2.readLine();
                    System.out.println(s2);
                    s1 = bfr1.readLine();
                    assertEquals(moveToSend, s1);
                    assertEquals(moveToSend, s2);
                }
                if (!game.completesSquare(move.getIndex())) game.changeTurn();

            }

            //Check that there is a winner, since in our 6x6 dots dimension there always will exist a winner.
            s2 = bfr2.readLine();
            s1 = bfr1.readLine();

            s2 = s2.replace(Protocol.GAMEOVER + Protocol.SEPARATOR + Protocol.VICTORY + Protocol.SEPARATOR, "");
            s1 = s1.replace(Protocol.GAMEOVER + Protocol.SEPARATOR + Protocol.VICTORY + Protocol.SEPARATOR, "");

            assertNotNull(game.getWinner());
            assertEquals(s1,s2);
            assertEquals(s2, game.getWinner().getName());
            assertEquals(s1, game.getWinner().getName());
            assertTrue((s2.equals(pl1.getName()) && s1.equals(pl1.getName()) || (s1.equals(pl2.getName()) || s2.equals(pl2.getName()))));



            socket1.close();
            socket2.close();
        } finally {
            server.close();
        }

    }

}

