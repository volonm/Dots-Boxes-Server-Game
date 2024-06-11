import java.util.*;

public class Solution {

    public String minWindow(String s, String t) {
        if (s.isEmpty() || t.isEmpty()) return "";
        if (s.equals(t)) return s;
        if (t.length() > s.length()) return "";
        Map<Character, Integer> map;
        String res = "";
        for (int i = 0; i < s.length(); i++) {
            map = new HashMap<>();
            for (char c : t.toCharArray()) {
                if (!map.containsKey(c)) map.put(c, 1);
                else map.put(c, map.get(c) + 1);
            }
            char c = s.toCharArray()[i];
            if (map.containsKey(c)) {
                int k = i;
                while (k < s.length()) {
                    char char2 = s.toCharArray()[k];
                    if (map.containsKey(char2)) {
                        map.put(char2, map.get(char2) - 1);
                        if (map.get(char2) <= 0) map.remove(char2);
                    } else {
                        if (i - k > res.length()) {
                            res = s.substring(i, k);
                        }
                        break;
                    }
                    k++;
                }
            }
        }
        return res;
    }


    public int firstUniqChar(String s) {
        int size = s.length();
        HashMap<Character,Integer> map = new HashMap<>(size);
        for(int i = 0; i < size;i++){
            char c = s.charAt(i);
            map.put(c, map.getOrDefault(c, 0) + 1);
        }
        for(int i = 0; i < size;i++){
            if(map.get(s.charAt(i)) == 1) return i;
        }
        return -1;
    }

    public List<List<String>> groupAnagrams(String[] strs) {
        if(strs.length == 0) return new ArrayList<>(1);
        HashMap<String,List<String>> res = new HashMap<>();
        for(String s : strs){
            char[] chars = s.toCharArray();
            Arrays.sort(chars);
            if(!res.containsKey(String.valueOf(chars))) res.put(String.valueOf(chars),new ArrayList<>());
            res.get(String.valueOf(chars)).add(s);
        }
        return new ArrayList<>(res.values());
    }

    public static void main(String[] args) {
        Solution s = new Solution();
        String i = "ADOBECODEBANC";
        String i2 = "ABC";
        String i3 = "dbcxxxqfjsdauxegoblxtcupxhrjmsaqocwhdnmuxrcagirtdkvvjplqqvomtwadpwqhouxinpqkldhotlqqljmsgexhhsfrqwhhrtqbmsvwrqvromnxbppernlhjtwdxslputqpuckejqtldedslkmiaplfbmexmjfoxtolnbgfllkdlecbjcunmlgrpdogjdtgkuklhesphablolsusoxtfbuldaeamrigmfuirwmdfaqkmcutapdbdafmumggxtjpgxntuuokmkpavbxgjucroakcmhfwqqaxqcmkabisvhpfaxuvgodcnscobaicqbexkfbhvlauagprxerbguxebofruipiwvvxuafidcarnbqmqjjalpuitlecfwtsmnmavnxxjxqimfapewbtdoemacgadtspijqagjhlrswieukatsllxkxblllfpoxhtabahxverkelgodqmwooxlehtfdqcqxrfcabimscsqsqkknhassgdadppqhbcjehobecblvetlopibhwqvqrtsehqvhppifiokvkjkxmomsiikbtchwbgiqbwmbetodeuqelsjhjbsvdrweqwjpnntwdruhpmsfljiiucknevoaqvnxeotaniswpigibuvdovfrfkcjdcabpcgcwqmljpoienbfajwvdifqosuuxihsajsfawnpbkxncogevewutkalpbfvqxeldcibbgvnfamfauvhqeuhwkinqjanxowtjujgbjnuflwwixfgrtronscdjalsswwkqjusigumjjecjwwhbpncwibxcpowtptqbhchwxlnjdpitlkmgbhkdvsatgsbqrggfhsmtksiviorouofkrqociioempjlmhdcrfkpiqewcsdccfalpxhvdjcgtuqsxfhkedxcrorkpsiivuxtknudmfdxbsvpuilustfevdakqhigvgsbebvumfbrxibrjknpjwmgtiahnbknjbpntutxdrfcfhlqhqqnstlwfurpghwotnawqgmoriwmsgtuwvjnndknjquedkuxrdeglglqgtmfioknnhshcfjeauavlrfsuduulfffjrahfxolnoslqkrbcxvspfavtmpqskevddrrsacgptcbjciwwsmsxnvkipnkoopbmiplxctojwrjtebsoemhlcfajdwtqqghebtfeeddlwplxqbfqwvqdeogajlbqrkitodhjxbwxluieakwnhhvgclgtrdvwjcmagcrncfndpjgejlhfidwgvjxscwxjhhevkvlbwqbbqfwfwnpaaqdjecjpnfqkthwibonftjdhwqbrehwfihnaqfmajhwjwumbuupriabfktnwwbugawssqdqpomtoageckxkfvonndnumktjbpplrncvkoffbqlqkmaualswgsgunbgohwkjtoftcpbwspvhaboodkedphxpqcjrhufsjmjlgrqnqndjfsrrokfwjrhmuffdtksadpqlivdcmjonbhklrblwmjgdcuifjhjjboregkbmglffupawesjdqouesemnkuaxdsmxjkcnwuaqgttjodunubcolibmwbjaasskbkgummxwokmlbugukcxdxgftvneorhkxwuojhklxfnkolxgiiaelegkbhixigaufairuihdedunbfrvrplqmtbqftmugxoblowqgxsilqwfmherioudxehvrsgsaejatjfsvuubvuddpaqmtxlfuhxlufrkoeajmjvpsxngkomgksvwlqxhlukrgrdlqbeeggxhfhehlxjpntsfjtrqvshqhjufwjekjaddxwrngxrfaepltorqicxhxefaanrsvoiswkgpvwnqlvvqdsnigesgojgvpekvsbpuemanwmuapfushgahvixfuroljaqcqjpkhtcalrxwcotljuqnpgovrugshhcjhojtjbkgluobootdikottvqfvsvtccrkpampjmikwwibbodimbriqpffrcuvqjvgrwbpwnvjtxnxfgeumbcmakeotgkalenmdcqjsuqfuppkqvvoscaqkxopnmafblcuxkiimblvivtsmfpxftutwfdqfvwdufdplprruulshtmiaeswfofvuoccvjlstdrmjrnosesdchidldndcbewealmlphlovddpxrgwkiahsxtpcjwvvrpwupgrjemndcfhdakqwvjpucidrnimkdhcsgrovpiqfgbqtiirqaxknjlpakiaxlgbshmrmtuhkwxsabkxarrjudddohgcwqfjelhuwwkketxfkeqdwbhckqjhunlafltdpjlokqjjjucbqbbwbisopkulseglftjqmcwhckkecsxwuxvwsnrgtguaadxewrvglvdxmetdwuhmmhevbbmroxbuwshkhfrxulpgrfwhxdbtraorglmwpduqlcnmsonjpemvbftwtgflldmeqmipasmnadbuneholpjsuoqrdodmkxgnatitpfjbfemjbarfjfwocghbxduxvfklpjfkvumwkwftwckgrfukkfimpmhcvvsilontswmsprmcesdatqkmnerelceglgndejtqfurhdmbgkwtvxniwtsmqkumunqeeesmiifeuihfhcrkevfxwuriivlottnwtrlcurcmaudhncbaveaggaowleokkpklavbecjsrfaaaatowqvffuodfdhwblxstdgxklaotsefgivstgamncxanhotcfmlxnndvxvgdppdtfxciffxvhdmphamvxonwujfehkbqmtkpadrlodlntcqjlpjklfjrjmgabvitbgjbphmgsudfoeugtjucajhgveohgpstpjijmuobhofoqqxlapkmojwxgcmlhqaiuuihfsfkhsbhbibcaqorfxxuogrmlircbwrlmjjliairrkuseggqgbrdliuargocwrcoqadmupclaxntfpcjpivwhpojteopmlmiqqtdjrwfwopgjedurlceinwwaqlrrvopwbikbmvhmjhkkvbsemjwaafaqlsjxpbfjdlaljokawihwkdsjjstgrlwkvvoeqebjwtohisnmxqwxdkeotmdcapaqvuikkiegcrdfbqiwkxgdxfjfcqpmukgbfgaitnniwepfljeipghepviuwfnmhtbgdufgmceptntpqfiaqvrrlrbnouishtivagptvibtrmntwdeatlnslcvxeufgnbehudwrggnmiqxbgtjxkbdhpalbgwwijgeeottxpvxlhsbbhgnntwjagctnvrsrljqfqhvnxupwabsmlmlbxlrnkafsbwrxsmqqqhvmpmohbgcaafaffqkwrmkakvudpuvwhscsxntmdajwihoqxmutmlbxxfsoktgifrmihwwxoqipbvesthinsatprplwlrtvsttgpxagsgobtndukcfcvrxiacqnkfmmfjqnojilwrdgixjeunmdtgftepqkhqchadctnugvdjanhnjtbhlbnifonvdejkvvrqjjmpttciloxuqbirusdpaccvknbctobjwildopqdhqrhapldhavsvqvhuehqwspvixkaxaivjvvditqekbdkugusjrlvfivmhningorutetdixaexxuwgwipbevjbtrauepsercimvkvbblufrjhkwrfnfmljqnpftniirusnqljslaefhsmqqgfmermnihjvstptopcnvhaturdwrxgbsropjmlvdqxbjjwujdxmfdcmlecqxafeoijeunrsrxjdagolqijsgcowccqtrmajlmvgoeotdwwkhuxiufcardfbitoihfhrjntkfijaptohwbpmgdinovwtnheobreciclcklckxhtqvobousdjojkobnjwprexanuvwtlajkkimttwqkmnxhbrmwnxbmsvruxtxrjcpmomlxgnalkadpsuoljbquewditfpupbxmfwdmbsgegkbjnqxrfekhkrwrrsfgselthfcivfrxquiuleadijaonotxisqnvtcsfbcmjwjcxfkkmrxqdpljfwijjvckgpupxtriogooufojpvfpooribiwiumcnvwrkekbttuhkwumcfklbxxetcmweqoaottrvfgixbjwiwlumfahobjtjxlongmuvalugbqisqecgurgbiftwsuolruadnnoblashroqnxnufxxshwlfbdqmbxhlgojglfrtwutiixmcnpmahocxwlwhlkvgnaqeuooptteqtxkfwnqqbbiiwlngjsndjulireiwaglqoaonqrlcnohirsgrkgpbsjjlncobumpaqjbtskoolggwhraqioeiabtlpgjwwgjasdjfnbivcaomqpttbmsidrxbgrhxxlhqefafbwbnlvgjlfplofmrctpodkscpemaobgrohkiouovctnogexlxpdqwbcjgavjqmjdepcedgwjlimnlpvwqerbhavslaubbadrsmjlcdhlpvmjdgnsvldivvnxxeqrsftvcxqmksqugroaxcxpqeamcqjptdjcdkcokpwouusmpnbmhlmoigrhesksufqkuqhudftdqiteuqvdlidfmrfamtpantulvxcxeqikgpvctttxtcvonwexjcarvfvmooexpjtdoaqqfgcowqqptvpufhfvdslewflesxxgiukujiscvlwsgfupwepmilhfovbohdrlllnijcekicgnvxwiowfwmijgwwwndntkqealmdxgxwbsssspdiadxahhwhbrjmmlxpmmbmdgchwqlpsuwqwdrddafrctqbuxqwavbmqsqmfhjovhogsxrsmbvljbhdmukwufmuxclnphuglrfdjvjnlsmgpeadtlhkburlxojedhtxnirhfxxlgdlktvrasnviwkskjwdwjkacsglrftuvhekgfcsdpinqlxnjldigbfbxcjtsblpsgoilwnnmmwhtqtlhilskejxvgtbbrnstkppivnrsjvkjwgennphsbocnvsuhgtlqtafgsjfvmxajmrqsuiqpamkxhqwlqudirctugtkohlxdkkxxumfjsuokfengvacmnmbdhsinbbijrcilvnghomqoogsihhidwvpsaopctqdbasmxiblsvnwekgfivjvnmxucwpolecilxqlldkdrvabermvpqoquhjrltvwtmgoqxgfwrxhvitanmauepgcoicoewaqqduhphkjqpqpnvqviccqqkbtdpudwiqckkfjbpgjdpvtkfwgemcckbpdekwqixomtaxvgibdmiwlmpfvcriklvqsrdiflvaiiwtlnbdqwddoktuqsreacfvhbbcrgsxmmkrspkuqhhewmcnptmhdqbeeunefcmeseocdttetxmbrelpevlxuvkhxufwrwvnalkmhsvdixckqpgkosfgdixmroljvtfmphubuupbjxkpcqdouxscikivrfhtjjshgaghlqkgmwtjjftuxhdvlsgajxqfuxgqhhqqdgvkkfnglofkhphnmjihxugqpgrgqmikwhafsdbpbmsbtcwmspojmnrksvjbsgqpcldxojwvtxqbfoajgtqwiksvfnainwxgqrxbeouorojdltwuqvhwdsaxagnnrtgxacljnduelkvngsafqwlrfglslxbpnwussgxjbqvoikcjwduugwsxfflnfqlgdorpnuexamherpcvtvmrjmwqmqrhpstcjmowcmjfshdfoqnlnrpmsjgecomcjvruiabhshwsokidpgjktwfnbukdxqnvlqwcqjuckvmfongfmjajofpmggdvtgdauejviihpvvkqaqflmibsogerjxidnxwtoqsgcerxsiqkurwvrdnmdinnjgslwugohnclmwcaifgtudqlbmdpflqwqdhxxumcalqnhvkuafflpmuwfilldrhomhbvfihnjruflkkjspmsmnqumsvqohclwsppdxaqrapkpfjjgvuiunogiakwgqphvtctqcndkhqdffxsmuuvpugnxkrwdrqqltrtdbapkhhsdcnwlgucnuphsrlwnvfigceovljckhngsgreftuvvtqgjnghesmwhpmmgawgcarhsgodisfxrjequvusxaxcosqfojrbsjdflfrnnmgjppqxdsnvxqnttuiruocvrdtqmjurtqxjieojflpbukxdgveacghrigkqpsopuprbmroaljehwvurgencossnxrxfsjqxwbtasoolvluousuwfckxjscqomdxwgbjkvvfeciclcnnajxqjgehlfimnjeodaboqeqsiglfvwjwaaoqkjjcudtiewmcahieifkwhbimcopqvkiocdtbtvlesltmxfxucbgjjeopmsatpfndadcsbtabijicoavonpblwpfojmdhncwnlbnpwedfghtwoqsdsavmfjfbkbiejasnepugsrtjewmgxwprrdrepkhjoepsjhbulcprnsbnsgluqjdksbgluusextjbobmrqfgwhntshorxlkwfnkcbuewddwvjqusdsgkxhnlgmxoowjjjjvhohfmplwethalutnldoabkjiqdcfdaptvtvelwxtmnsgitbthkmpdxwkbvppurpltgfulspupidfaanqiurrtmlfqmvgembwrqqdnrlkffqxtcodvjehriiigimternthsojqfceessjbtwuhbpalvudkjlgtittgcpxmfftobqndkuneuivtsixuhlosrkgmklncjuwtamdqxxthkqnixmueselimdlujbkqrpgrrmlrlibflpbluqrtcogvjgclochrvgdkdrevmpfqiubljtpaaahbalfllwtkfamfwegudlhxhreqghvlkevnsbjtpvpnrpblckkgigakjmkstsmvkqbinkjmkpdjjrulpoiemoachwvsifefgvdkkusvelohfpsvnwxvfugophlpfaeliljmcqhofdivnqgjmmibfqlodhmkskniocwvdgopffcvcwwquwsrskgdknbjqnodcbqnxfqrfcehshsjvfwewrqultrgfppmtbqnfpuddkvbomlnhidcqxqjixfjlbcuqkfumksgiewvxnbkdrsuicxsacvqqlvkdmqsohmiebpllkdtxotqfdfilmingniglxiqcgxlqcpjulsnninrrcrkrepalguaqlouaxopcnojrpfcdhaedwujkebhrhjbcprbabhsmsvdshnqtlgtdjfewsxepqgarececwcovtunodrklmmvbrnlvxqgnjlwokjpguilugcjptkvnjvdopdwptvgtckkhrvjmmbpdvaguxilqthlqtignnoljtbefrxsnwmurgfnngcemccxqntknxsnhdquabwdxjcrwkcusciwqgxpwufkaxcmntitbstddhkxcqhglbltohgrlbophwvrllqioefdcwnvvstqbmdcnuwxnmfaqmedbtrlrhvbspddhwguscauwwibwvlvnbgdqtlnildpnklbqnbbxfbxpftnumxxfemxokvvnhgfroniaxmpjlonbjavbjcfhpojebqdpmorifcppegxgfiwekoruddxvqljlqdxotevjnkggtiaadxbixopnldowadvbxpkscaiuxuwlwbkfnsowcajdbkrkxihigmlcrkdjljwxlkgplbneblwinpirmpxpnjtikavxbrxttdlmeopevphdplltjllvdgrmtvoaqtpggtjojhdewotegflimjvubefmfpwerxipllbmcmrodncllwhiguutxtpbqwgrnojqecjgxwjrgxmaofitpcjcnkitmmnisataxbuuivenvkkehtekotdrkspcboebiengvhpoeicrbglfwantnrsaikfhwprujlpmovmuvpjxcmxmctdpsrwhnliqmugctekjsckwjltghehknuepwnagknshlqlrxievqhjejupgkfsffucjjvxvxpdklrwtnoiarmsxecgxjaixdtfhdjenljrtehjofhdcwiuveeojnesgoadidanmifgivdeehdhenmqxhsbfocxmamgttkelmijtanvecrlewpeggfxrurxqphgsrablqndddmwvqkxtdskijnhowsdrmqbmockceclapborpnuskeshqjrvvfkrppjbbprsqxjkdtghitrpugkjlbfesjehqvvjmaoclfgbbtvpklwtrquqjpmvcxctpsounmpjweqvpitrxgmhrbhdtbvoqgcflnssomwrjdrogdbvveccucmsbpablxovopulnhcrusjmwmfdneitbksftkofsrolopbpcgejpdhxxsbtpoxmjsrebjfbwvjadwdphblrsltirwvflewmfrspcwqhxcpchebrlxxjunnndhasrtvlkqdgqomofjisjqtonbirwxopwwcaqgubdgojbttgasvricsxwohrijnhsstrjduohulawnepxefffmfsgplkcmslxmutekekvsbdwuqbeaqiaterfdmkuawfnuuqreffopidtonmvfxabkitstlkvmqutjdwqropkmiwlwoilmrhpwipgohtgrqhtdbxiihqbacnhkagvmwumcehkvrtiohalepkscqrcmfbpdvufwxowmuseqhuiutwebngxwcahxbqlqmtbcdpgebiuglerlpbgnrnefuhokputbvesxsommsjeaufskqjionwuwouqvgmoarnigudhbincvtgkraoluqjocjjvhgifthilgkwjnkuqwhwsroqiatojimmmqxpikpmcalhaiqomlaxcccxvkmfocxhpccthwcahtqwnkclotxactnecjgpvvdbukglsogwaahuijjuqwljbfgfbnwsglhbmlmxqmonwochaqehqnmkrxodqqwxqmtjhldplfxfjojihndfqiktqklprqfhnaxqektljtdgiatqlbphggwfhwxhcntqtfugvremlwbafdafvtxddapgwssnlqrtdgjliqhaiwctgqqrnutdonnpugcxoigbfrxhwodakbvxewesldmororilujhcwsriwulxeavpkcehoskorbtslccbjhewsgkgpdvdjpvrxrtpxnxqnsektjdxikgdlbofjbokwhsnjtkdcsdpiqirgunfpuebcdeopiplkakwhpsfptvmskxponglguiawemropwholhtbfetnxvxcqjeadiqodjxifworwfoshhlrogonptpicwhxxsvxhhqqvkuwgsafmmpvrkwokhgwjwriaulilsjfvavfghfxlvingokbibkrmjkogvprmdthuipxgcmjdclsoelnrbmumhspshmmeafxsclegfgdmdtlalktohmfprjdsbjwkcbnxwrlxhtvgaokmlvdgukepnomjdvcgkvqevinrqtnkrwuceeucwnsmmdpuorwrotrafcjkawgxobdtwjgawoxmxgwvqfcshjqlpfiehdwwxqhorlscfwcjuqrdsjhrwqlwmskgneowfkqenjaijcmdvqigmnnhkhfqsjwakpnpwrmesmxiefuqrasppqltkambdbelwfdjtdooauauvwlchohfjdsnqbbkgmfojnsvfcmkxattteibrlaitxbodldklarkebpckthrqcpoaaedoxvrorrvdgtjjgpnvpfaejgkbauutcxsocvxjurkikqicwarojcqbdbndtlvmkivbmbsdpsncwlffidgnngatqctptmkliivhmidorexreddklbkmlcljrptuaojqtoqqdtjbdgpfsrhbakpjvgwthqnrckntelierrmmvrwgrflcafngrrlbpwsaqptelwntolnhpesebwwfjdkcjujlmabadgflqqgwsrccaivhjvadttavlwbbeqsrtxsjlattukgnkuxadbssiwwoiqctjlnsajsmdhmmwpwitjxvvtdlodnphkmrrttvsmwnkfspghutuxvqikepglmhsdhlvaljijnnwbuwvlhwnfjpuxdujntgxdubesgolqxcqmkpksxjntluqccmessvhekuqxlvuivoxnvmxvfnglmowkinccccktrsxskuakoanvmdslaaokummhwjbesoadkuljdmsgshqexomnimotridcdhdblbijelrexfbdcfsjweftoxgmfrdthhwidmmqhfenfiubfjiusnfurtwvpxmctblkmncoeedrnturltfocjmbjwfhqknfofjgggdlshftaqrletqhpajjhsubxsapqdkfhnxijwlifftwrjqoacnnswuvepdgbdepbunfkiwdmmblbnxufpqvkksixbpkknatdchruplcgunjnxtqgicqiojnjamnsjwbowdnpkvnkmvbtxelutdossabrfbuchwljcsqtjsfaoklwwengbkalwghhoasipaguvmtrmusqrewdkkvetqoqcufmfhuwktnqxbgqlbtdvsceuvtppnxdwslpipvmwaweaaqrpsjisorqfwiwxbutkqkajqdivxbaqcjswotiqgahdvejbemixwkaokoevapehasnbxskhdkkicxbhgattdcojmpaitqbfpdsrdgoifuqcepfqgqdpatkrhgcvxdgtsdamuombmjjtvhntvlamguvflketfilxatpuhsflxxvctvkklblikowpamvmojrcitppxeapaofhprtequdvhinggdwphuhvlcixljfdfhqsbeqbdrqkmdcknigelbvwrqtksenjhcxtqgjrgtloapgtekvdrjmpcwqknkxhfobsogpmhaldmlqbustuqldooevwvgdpbmopbfjcpqqaaajvfqjxjqsfebuoxgsijlgsssiuousvufqvpdwmmqslnwucwkdbpusdrgsqmmscptncrulmjkkqbkgsbdoubprcfbbpiphxdjqevshvxhktiwrwxruqhdmaasvclfsewicmrwcqagtwsbnwrltflqrlacepvikrjqsawxuocalaomccpsotlacvwaiignxomqisewwnonmsohrtrvcsrihmcublgxruginrttphmuwsqbjxonjcltwkeankfmjbrsamsvpktvijntsxpkktkgjntkgmceootdbfcuoqfrkpnmventngveaxbctqwiqufgalecnqiimmhnjmgatbotrhmjvijqqbpqwgneekfbprmfojkddvddgvnxddllvxjucvqnjvefcenvnrlbvtfgojmdvrdspfsafcelglvefxifnwxvcberkdavuctupkluofqwsdpvbafuopamjjiwbddhoobsuqnknefpgfeafrgtjmurssbnlrdwffotwwvhcitoqcswrrkruflsgdooqfjfricanmwgojkktichwhqpkkhhegqpbhfkrnurckxmqxsleiuslvjeqtpjusplvphvnvovuqpurdklfspqqkfbaacqxxdiuowxfjovmghexddqnxvqvwtfrjjdlfmxhcdakxvabmxmebvkuvellbnjewmdlmjxfnxxdbdxltxfitqklwfirtjfxpdpeetiwvhninabcrxpbtupjqqaiuiiuvviifsuluojsvlxxhgbrxakwfmtpmkddglowhgrdidmqqwqronehjgldtdqguxnkdgiokppwlvncvpoauvheiubpedivkhhtfugjpnxnunvqopgvdlthedvcpfcnhbqgknkomxjpdtetcokxbkpinsgmmbpvmwbbudjftomeipjkbtkgareildvolxwnxwsgcmgpcsaulbfgdiftxhsnoeshugigsrcnmkgdtlgaeapoidefvfqbwwuqhhnxdokujlebmaoxtnikinpmmlpetjdiedeqexbfdpochlqcqipkmwvitrwfffqhdiokukxpjiundstiljnxknwscogevkdnewktlagllnpcagxjuqrqlmdbbeorrxllqprorbmhrfpcwxnnmmmnqbegirhvsvrqnrkawnbolbluvefvbpoxhfaaxgjhbunmmowdstofcbmavpgqmxgnsaqpxldxmufagmuonftoenbwowroofvhpkttohfwnnelstnkpbhqcmdxqcfaoacgackfneqttwqvxfrfiadtnhccttdnlcgjeknenqmwvrsphapjqrwqlxvppbkvhrqqsadammrqnmrqbwiohgbowkexftdibxbemfmcmivxsioqmvllgflvmibjdsghrsbujikrtulwmmqqsobithvohdrokxskwsxartsnlhrklkagcqjvimxqfjxedihpkrmqumhhdkpnpinnevetteidiuiffvhiufhvcfxwlghwqpasalkjwhqipkxqpapefarglmkcsaovgprxwtshqerfctcodhsltijuqsjtslwtsihdxnunqfqnrbbgatwwhgqnhwekkophsktwbjsmqiqnudfqvulmbrwdbssocijkpeurnhrthfxhlagfeckocdcohulqcktskatdtgudvwnsobdemndsqkemxnjhlunrbehfmxidcktwvgnvvmvkmhvhtnjltgahgabvocatwijebpdixbrwpcfhbmwulaekpojfthctjbotatgolkwuidlsdjgdurqmwfoucwpednketlgoxinwwjasivjxmtnnseadkogvnmpnlqcjukfelwewxjaaemstleijfqxpvftawasvkspewawpsdtpvuaaangwsnmqekovwtaeswtioqoeidblwvoldxsdrckclbjcbtbgspixfonfjllmgwfndjkxccmnattjboabmnocsrttnrqlhofmqmbcveahviwbvokpgapaftpmmpbhqgftdrnesxwsbpxlnbkisairoscsgdnajoohkgwwrmpodkigjpgcxmevwhlvufngcohkglgpkltbvxbcbkwhmfbndcdeexrslfjtpccavubngpcavrdgdlhigkcxpiqdenlsgrvhlgsbokrgvtvidghwxjxgwptknegabcugktngnabwjrlumorqpfkkpvjnwdkmrdknlrdddqiqrlwsosmvmhvkestppcgohvfshjuaatodnjncrlrvqpnwtginaqchspnhetxvebvxwkjffrhrjnfhoabjcpxgjtdempudpckekhcktmharbdeurwktfntgxhpomubjwatcrxcbeikhkpfncwqvdlxqeqkrtpxtfmthgidaadatjckqqruobkjpkpupeuwdorupwhxjkirmoduxgivahkrlbdgxhencsnpedjwsaonerusjttljeshmqvhbexfrbilvdrwvtomcjsfoorxdjkecbuhnceugdtacimjidhpgqhmoqtpfhlxnsbgdtludiwwcanxnxkfamtpsbbwpenbnmufdfvmxhqoxdcwkbwxrgowarkrjihishmlnrsfsbkhqllqrpmmxopsbqgcdncwnckbsxbglwlknxjebstmluokffwavjgdepfwqwtxmoeggoelskehnhuwvssupfsgaewcaqxburvldjtuewhwoqrxpfjebrgpccenllwktofjfqhxhitquqeunhmllntoqjiqhqhnbhmbcthmlgjvbfwfnhswwrbdmacsohdxoctcdjmmajaodxotrhuxiuppfbrlwpckdicerdowwrrkeiffqvsfcqosccvljcdvgaqiksmlgodjdgktssdavtncnuilwgxaqegvamojoxxuhcowggqjhfvbvhhlfenmbketrbvkxvfjkebmgjqpsqvgktvjweoicmjlptjocrullekajldcvtocmpipiwbmrinuiartnqfpskrhpldlhfqulvqevbhraobookotsvpxxvilqkoikpsmptwjexqwwqnkapawixlcsoedfqmenjnkqkkmgwldkmqhohosgfqrlfaxuvweadqphcdabhiromtfiuajwixslscqwrmsteukksjsgbjxbgvmwnxspaxhqncftlnfggilcuwunglntlxviblobvrqlfjhmvrwrxflioavpebdmsjhojtemxnevupepnktealjcbpnkfrcenctqniuifktmatwgevohbrfcnmvixljtccipnbwvjbnskwfxjnhlbhagbgmpkirrcswbaxtlrjsvbhpuwanwcwjqpwkbiaroncvhxscsnllpxxguboqjkoihnmampkbctrwcdbukphapkvbptiavswgsuhfkrprgdaiismpegtpmmcjeuggikhcteqbsuwcaphdtuufwbckidwvvehrmsbmrfgmmbatbnvajtjwsjkikxavrtmbqbteexshqxumsoknefcrowuckcrjiauotantmburwqloccpnluqnmahhqsaskeqrxqqajedlwceqaqmvoglnsgehmrohqhpcthemmqxeiobswsqhnlsgkkssgvsrqrkphfiwlfjeeexvlwekivvkdckbxxvxtkjstefohcrlsmaagnhphlvinpulvgwrjjlkhkdmabgslwmlrxsncmkjajhrjuxplhjitiabhibifrkwtumurbdmlptrupfcxvksxwpmsasfsglcmdgeekjjjljfeicjhahkuewvdrxcifxgefqwdhtjhdbvlpgejdxqikwvjtlwrgvltdjjhxkkwacppmqmpvddehgldneblrnhstsfglowokfnkgbxivdlbnhptaduanjvpfklrewvhjkglpbimmgafkarimpghmokdtckjqkgsualbfxuscmtsgsckrbxhmpahdbkmhdrvfptorlfmpgdodujbhiqkvrgjoqumtjwjcaoblwkbkuatqxxvwfhhbxmcuhpisdwxulfkkimrnfcqmddgnpxoxxldfflqwsqnchwbqakewkceaxvefhfpwrsdjtjlvgefwfmgdxutwdarmmnxofdcpwrbpiqdpgcgwemjuekmfxcgijmpiqqasgihifqxostiufikdifitwcltxbetruhpiieurrxbthcoihshtmxprxaxnfhwxaivfjilnmlxjmgmurhsmpscajfkeoocdluwerdfaatbtmtqrxckthhecbsfdgdxevbiocfctgixsobbqiuqkdivaoqaefuvthqmllgrwmqrnlaojulmgllnsrvsubtuaqcssfolaueovbbilubwkakmgasnfugtkiwkdgvqkovhcccxxhnwlbmrhoipxvxtjqtdhalilbrntwesvfolmwbndanbjvnngplowtbcuvkwauhtehwwtibitqltetixjnvlpvfqmkgksmequmexqflsweanaxqrstbkdijquqxtbobcgmiweqrsfxoomsvfxqptrettmidpudijspccpgsshoexispjdmxnkhnblcmqekxvpwsfibhandsjfbowuxbswlvjjubmrligwainiawngfxcdpkmckvqeqnviikdcxctggulhdartnvsbdtthudifuudnfhxhuevqgopllftmktdqfcdigtsqbbeluqxjvaumlxbxxofiertqvfdaggnwogqqunsahfqbkvarirvplptxmfeewsdomsgmvwbdmdjhvrocmxmdiglqjdwhgqsjsniihlmtdkgidujjnrkkkulrefjhmjlgiheudflpnsabumswtoheskddwnvmslgowalhikniadxfblaluvkswjcfwkjhqacjfbfswtdgpwlrbifokavtihcqmmpqmxbwuacewrwaxbmaukhxmgoiifblbknoihrwewsopsugsvkqcdxxtpormehptomktcdidmuhbafbxdebmknogcnnotgdfxdtwhpvdabanrtrgbtubxbtfjkfgjfaenesioveumrrcxunqqhbsklwitxqcatgkafgbxmgmgmrircgejipwlsbircpepregahjrcwtfqciixdmklvxvkhrmrebdwxlqvkarhrsxikqbbpwtnaapxkbnmvpavfcbagvqowdaqfolgqmvjxtfcdhcserkdskqxdapieqcxlnobfxlodigukdtmdwbtacglaqudvomfutdpvpkuegdtwwaaaxfcfdjnggcipqhcaqbrbtudrnkabicpelxrkmttvrgiemkwgfjpruilupveriicxtwipoupvccjscvbasbjfbpmtjmvhxsabglxdrcpgrnfbtiluwdpudiwhgfnterqrfexiuxfpfhcthmudjxkhcdjqlkduqdujilwmitispikhnimmftapnqggtkotsltxoqgqeeqnwjmevembqrdkmaliewabdgnmpjfmjuujssadjbcasjjqisjioviulobiuivqpcwgfbguhgikejudjwbulhourkjsffmtvxvlnawwhtepnlljgfrnavslgdfukoewdjrjcwxtcjixhhgeqodkpfuxbqlmbvekcttbfmubhpscptmshbffqsmktbmtnrmnkkjbgisbhfmphjhtcxjmdbskdoabudmhsiujevkdcmfixiwbjhgjoewqkahfokustumlqqmpxtftgrrtvjmcukalxgcjeoumeosvrlanhkdrvsiiwftpllbflqhlghewohejifhubsbjmwdblmlsuipmgphmlweijwmvegxnojonkclwvferwimjxkdemsusmlijgpcqgskdhioplroordoeprkdbuumipchnhgfaswenhntwprpxspvnnlqbknnurigkwvmudqqjpjtoxnvgefdcfifmgvhbbmfffguterpobiikbshgjsigjqadqgqwqfnvtipvfjqjmuikgjxqcncpsdkgogjendotifdrpjvvqtdxvqleoocagbkmkxrsqoawumbarxuqohtbwjujfnixqksgeicrjwchifistfocfggxskcxxkdfvoqtcacrrlgolisworduvkwsifnifvfrxfweobsrxvskwfvmjnsgxkbkqafjwwmenxkqxkckeexlaucfeavhbgxgtnjvlnbvxmmiodstoqmsrvjrarsawgcgilsslcunwewesejnpklxrrspmscqlkrdxciagvuebahllnjppqcbjwvaqcfasctfartimxtbrwwgrwqsnttjifbdmjlqkobtmsdcoghueiuuvhhvjeuxwxhbjhdptgtwsmxnlubouejwgaortjokmkpjouonotjvlqqcdhjhbmfdnkewtmasrqrmuamtctcrgegahbxgrwhuadldkmeafpvksdvrippsdrraoqteouaijujrqiaubrccigjogqbhkpjbiwejpfjaqghptknfmfjnwhqlouwamwvuvclefjiutxfwfjduodssfpriqngwqxxjomifhinlerlonnkqacvkupnekrljwqvptutnfscgtdawuwjkquketnehgklihtiosseehpfuwuowjucjribbddwcdxiekoaqvwcropioxolhmploqorrlhdfkaqfplmctionbkrefaijnhnrhplltdkxsntkpbohmaqxrqivrcedfnarvbpimgebdftljamvbwqaerhjkergthtpkvnpmajkgthjfxhujsginwebagnbhgqchtmrojrlbeomtaxfnvrwrfrnlijfstnlteonhquugbbtukdqtvlkcqmmecfcdelboojebhjuncqppvnmvmswxfghkfbhslknjtovtoctfxdhfrtcdixxiwonnxvfaobxtjfjwtfcoabufgortlrinrwpobqtuhsomsnqqpdrqotoxvgcxtsphamveembgntkfeibdkuxmhsetmtmpciewcbgioxrxxvvnrmfpepfjvmocmeqrpuqqhvsarcroxaumisdtgvthorntgsgxcocphitwlublmmkdrkehohxpudrwigfadweksswrohkggamrmmpdwteqwibueofvrmdcicwkjjeafgfgbxniujicdkoeacafhhkwbbqildgabmtsqvgvkdmvvxqoweuikawwvhptgnaxdtgojebkhppcthwtvcbwlpssumrujhuujlabmnoxsxcaneqcevaqseelgaoceiahutoebxgvnruatfhdnfifpxuiusafhcmamnlnrubdhwojfrlxpsknthdruuefslbishmokspsqfhtdbtmcugbuorpaumlfuwgekexvloriqqwo";
        System.out.println(s.firstUniqChar(i3));
    }
}

